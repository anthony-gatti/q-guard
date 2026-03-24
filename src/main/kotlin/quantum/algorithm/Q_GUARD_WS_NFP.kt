package quantum.algorithm

import quantum.Fidelity
import quantum.topo.*
import utils.ReducibleLazyEvaluation
import utils.also
import utils.require
import java.util.LinkedList
import java.util.PriorityQueue
import kotlin.collections.HashMap
import kotlin.math.pow
import quantum.randGen

class Q_GUARD_WS_NFP(
    topo: Topo,
    allowRecoveryPaths: Boolean = true
) : Q_GUARD(topo, allowRecoveryPaths) {

    override val name: String = "QG-WS-NFP"

    // ---- helpers ----

    private fun fidelityAfterRoundsIdeal(F0: Double, rounds: Int): Double {
        var f = F0
        var r = rounds
        while (r > 0) {
            val (fp, _) = Fidelity.purifyWernerOnce(f, f)
            if (fp <= f + 1e-12) break  // hit fixed point
            f = fp
            r--
        }
        return f.coerceIn(0.25, 1.0)
    }

    private fun effortRoundsForPath(path: Path, width: Int, fthEndToEnd: Double): IntArray? {
        val hops = path.size - 1
        if (hops <= 0) return null
        if (width <= 0) return null

        val fth = fthEndToEnd.coerceAtLeast(0.25)
        val wTarget = Fidelity.wFromF(fth).coerceAtLeast(0.0)

        // Max rounds allowed by width: need 2^rounds pairs on a hop
        var Rmax = 0
        while ((1 shl (Rmax + 1)) <= width && Rmax < 30) Rmax++

        // Topology-known estimated F0 per hop (deterministic)
        val hopPairs = path.dropLast(1).zip(path.drop(1))
        val F0s = hopPairs.map { (u, v) ->
            val link = topo.linksBetween(u, v).first()
            Fidelity.freshLinkFidelity(link.tau)
        }

        // Precompute wAfter[hop][r]
        val wAfter = Array(hops) { DoubleArray(Rmax + 1) }
        for (i in 0 until hops) {
            for (r in 0..Rmax) {
                val f = fidelityAfterRoundsIdeal(F0s[i], r)
                wAfter[i][r] = Fidelity.wFromF(f).coerceAtLeast(0.0)
            }
        }

        // Find minimal uniform max-rounds R such that product wAfter[i][R] >= wTarget
        fun productWAtR(R: Int): Double {
            var prod = 1.0
            for (i in 0 until hops) {
                prod *= wAfter[i][R]
            }
            return prod
        }

        var R = 0
        while (R <= Rmax && productWAtR(R) + 1e-15 < wTarget) R++
        if (R > Rmax) return null  // infeasible under width cap

        // distribute effort downward while keeping product >= wTarget
        val rounds = IntArray(hops) { R }

        fun productWCurrent(): Double {
            var prod = 1.0
            for (i in 0 until hops) prod *= wAfter[i][rounds[i]]
            return prod
        }

        var curProd = productWCurrent()

        // Greedy: try to decrement one round at a time, choose smallest harm first
        while (true) {
            var bestIdx = -1
            var bestNewProd = 0.0
            var bestDrop = Double.POSITIVE_INFINITY

            for (i in 0 until hops) {
                val ri = rounds[i]
                if (ri <= 0) continue
                val wi = wAfter[i][ri].coerceAtLeast(1e-18)
                val wPrev = wAfter[i][ri - 1].coerceAtLeast(1e-18)

                val newProd = (curProd / wi) * wPrev
                if (newProd + 1e-15 < wTarget) continue

                // Choose the decrement that drops the product the least
                val drop = wi - wPrev
                if (drop < bestDrop) {
                    bestDrop = drop
                    bestIdx = i
                    bestNewProd = newProd
                }
            }

            if (bestIdx < 0) break
            rounds[bestIdx] -= 1
            curProd = bestNewProd
        }

        return rounds
    }

    private fun perEdgeTargetsWeighted(path: Path, width: Int, fthEndToEnd: Double): Map<Pair<Int, Int>, Double> {
        val hops = path.size - 1
        if (hops <= 0) return emptyMap()

        val rounds = effortRoundsForPath(path, width, fthEndToEnd) ?: return emptyMap()

        val out = mutableMapOf<Pair<Int, Int>, Double>()
        val hopPairs = path.dropLast(1).zip(path.drop(1))
        for (i in 0 until hops) {
            val (u, v) = hopPairs[i]
            val link = topo.linksBetween(u, v).first()
            val F0 = Fidelity.freshLinkFidelity(link.tau)
            val target = fidelityAfterRoundsIdeal(F0, rounds[i])
            out[edgeKey(u, v)] = target
        }
        return out
    }

    private fun hopLengths(path: Path): List<Double> {
        // Each hop corresponds to a (u,v) edge; parallel links are assumed to share the same length.
        return path.dropLast(1).zip(path.drop(1)).map { (u, v) ->
            topo.linksBetween(u, v).firstOrNull()?.l ?: Double.POSITIVE_INFINITY
        }
    }

    override fun P4() {
        majorPaths.forEach { pathWithWidth ->
            val (_, width, majorPath) = pathWithWidth
            val src = majorPath.first()
            val dst = majorPath.last()
            val oldFids = topo.getEstablishedEntanglementFidelities(src, dst)

            val hopsMajor = majorPath.size - 1
            val FTH = fthFor(src, dst).coerceAtLeast(0.25)

            val perHopTargetFallback = if (hopsMajor > 0) Fidelity.perHopTargetF(FTH, hopsMajor) else FTH

            val wTh = Fidelity.wFromF(FTH)
            val majorLens = hopLengths(majorPath)
            val Lmajor = majorLens.sum().coerceAtLeast(1e-12)

            // Per-edge targets for the major path using length-weighted split
            val majorEdgeTargets = perEdgeTargetsWeighted(majorPath, width, FTH)

            val recoveryPaths = this.recoveryPaths[pathWithWidth]!!
                .sortedBy { tup -> tup.third.size * 10000 + majorPath.indexOf(tup.third.first()) }

            pathToRecoveryPaths[pathWithWidth].clear()

            recoveryPaths.forEach { (_, w, p) ->
                val available = p.edges()
                    .map { (n1, n2) ->
                        n1.links.count { link -> link.contains(n2) && link.entangled }
                    }
                    .min()!!
                pathToRecoveryPaths[pathWithWidth].add(
                    RecoveryPath(p, w, 0, available)
                )
            }

            // For each recovery path, remember which major-path segment [s1, s2] it replaces
            val rpToSegmentRange: MutableMap<Path, Pair<Int, Int>> =
                recoveryPaths
                    .mapNotNull { (_, _, rp) ->
                        val s1 = majorPath.indexOf(rp.first())
                        val s2 = majorPath.indexOf(rp.last())
                        if (s1 >= 0 && s2 > s1) rp to (s1 to s2) else null
                    }
                    .toMap()
                    .toMutableMap()

            // Precompute per-edge targets for each detour based on its segment-length Werner budget
            val detourEdgeTargets: MutableMap<Path, Map<Pair<Int, Int>, Double>> = mutableMapOf()
            for ((_, _, detourPath) in recoveryPaths) {
                val segRange = rpToSegmentRange[detourPath] ?: continue
                val (iStart, iEnd) = segRange
                val Lseg = majorLens.subList(iStart, iEnd).sum()
                val wSeg = wTh.pow(Lseg / Lmajor)
                val fSeg = Fidelity.fFromW(wSeg)
                val detourWidth = topo.widthPhase4(detourPath).coerceAtLeast(1)
                val effectiveDetourWidth = minOf(width, detourWidth)
                detourEdgeTargets[detourPath] = perEdgeTargetsWeighted(detourPath, effectiveDetourWidth, fSeg)
            }

            val edges = (0..majorPath.size - 2).zip(1..majorPath.size - 1)
            val rpToWidth = recoveryPaths
                .map { it.third to it.second }
                .toMap()
                .toMutableMap()

            for (i in 1..width) {
                // treat a width-w major path as w independent threads and repair separately
                val brokenEdges = java.util.LinkedList(
                    edges.filter { (i1, i2) ->
                        val (n1, n2) = majorPath[i1] to majorPath[i2]

                        val hasEntangled = n1.links.any { link ->
                            link.contains(n2) &&
                                link.assigned &&
                                link.notSwapped() &&
                                link.entangled &&
                                !link.utilized
                        }

                        !hasEntangled
                    }
                )

                val edgeToRps: MutableMap<Pair<Int, Int>, MutableList<Path>> =
                    brokenEdges.associateWith { mutableListOf<Path>() }.toMutableMap()

                val rpToEdges: MutableMap<Path, MutableList<Pair<Int, Int>>> =
                    recoveryPaths.map { it.third to mutableListOf<Pair<Int, Int>>() }.toMap().toMutableMap()

                recoveryPaths.forEach { (_, _, rp) ->
                    val s1 = majorPath.indexOf(rp.first())
                    val s2 = majorPath.indexOf(rp.last())

                    (s1..s2 - 1).zip(s1 + 1..s2)
                        .filter { edge -> edge in brokenEdges }
                        .forEach { edge ->
                            rpToEdges[rp]!!.add(edge)
                            edgeToRps[edge]!!.add(rp)
                        }
                }

                var realPickedRps = hashSetOf<Path>()
                var realRepairedEdges = hashSetOf<Pair<Int, Int>>()

                // try to cover the broken edges
                for (brokenEdge in brokenEdges) {
                    if (realRepairedEdges.contains(brokenEdge)) continue

                    var repaired = false
                    var nextIndex = 0

                    tryRp@ for (rp in edgeToRps[brokenEdge]!!
                        .filter { rpCandidate -> rpToWidth[rpCandidate]!! > 0 && rpCandidate !in realPickedRps }
                        .sortedBy { rpCandidate ->
                            majorPath.indexOf(rpCandidate.first()) * 10000 +
                                majorPath.indexOf(rpCandidate.last())
                        }) {

                        if (majorPath.indexOf(rp.first()) < nextIndex) continue
                        nextIndex = majorPath.indexOf(rp.last())

                        val range = rpToSegmentRange[rp] ?: continue@tryRp
                        val (s1, s2) = range

                        val majorSeg: List<Node> = majorPath.subList(s1, s2 + 1)

                        val widthMajorSeg = topo.widthPhase4(majorSeg)
                        val widthDetourSeg = topo.widthPhase4(rp)

                        val effectiveWidthMajorSeg = minOf(width, widthMajorSeg)
                        val effectiveWidthDetourSeg = minOf(width, widthDetourSeg)

                        // Major segment EXG with per-edge (weighted) targets
                        val majorSegTargets = mutableMapOf<Pair<Int, Int>, Double>()
                        majorSeg.dropLast(1).zip(majorSeg.drop(1)).forEach { (u, v) ->
                            majorSegTargets[edgeKey(u, v)] = majorEdgeTargets[edgeKey(u, v)] ?: perHopTargetFallback
                        }

                        val exgMajorSeg = computeExgForPath(
                            majorSeg,
                            effectiveWidthMajorSeg,
                            FTH,
                            overrideTargets = majorSegTargets,
                            defaultPerHopTarget = perHopTargetFallback
                        )

                        // Detour segment EXG with its own segment-length Werner budget + weighted split
                        val detourTargets = detourEdgeTargets[rp] ?: emptyMap()
                        val exgDetourSeg = computeExgForPath(
                            rp,
                            effectiveWidthDetourSeg,
                            FTH,
                            overrideTargets = detourTargets,
                            defaultPerHopTarget = perHopTargetFallback
                        )

                        if (!exgDetourSeg.feasible || exgDetourSeg.exg <= exgMajorSeg.exg) {
                            continue@tryRp
                        }

                        val pickedRps = realPickedRps.toHashSet()
                        val repairedEdges = realRepairedEdges.toHashSet()

                        val otherCoveredEdges = rpToEdges[rp]!!.toHashSet() - brokenEdge

                        for (edge in otherCoveredEdges) {
                            val prevRp = edgeToRps[edge]!!
                                .intersect(pickedRps)
                                .minusElement(rp)
                                .firstOrNull()

                            if (prevRp == null) {
                                repairedEdges.add(edge)
                            } else {
                                continue@tryRp
                            }
                        }

                        repaired = true
                        repairedEdges.add(brokenEdge)
                        pickedRps.add(rp)

                        (realPickedRps - pickedRps).forEach { rpOld ->
                            rpToWidth[rpOld] = rpToWidth[rpOld]!! + 1
                        }
                        (pickedRps - realPickedRps).forEach { rpNew ->
                            rpToWidth[rpNew] = rpToWidth[rpNew]!! - 1
                        }

                        realPickedRps = pickedRps
                        realRepairedEdges = repairedEdges
                        break
                    }

                    if (!repaired) {
                        break
                    }
                }

                if (realPickedRps.isEmpty() && brokenEdges.isNotEmpty()) continue

                // Stitch together final path
                val chosenPath: List<Node> = realPickedRps.fold(majorPath) { acc, rp ->
                    val toAdd = rp.edges()
                    val toDelete = acc
                        .dropWhile { node -> node != rp.first() }
                        .dropLastWhile { node -> node != rp.last() }
                        .edges()

                    val edgesOfNewPathAndCycles = acc.edges().toSet() - toDelete + toAdd

                    val (_, newPath) = topo.shortestPath(
                        edgesOfNewPathAndCycles,
                        acc.first(),
                        acc.last(),
                        ReducibleLazyEvaluation({ 1.0 })
                    )

                    newPath
                }

                // Build chosen per-edge targets: default to major-edge targets, override detour edges
                val chosenPerEdgeTarget = mutableMapOf<Pair<Int, Int>, Double>()
                chosenPath.dropLast(1).zip(chosenPath.drop(1)).forEach { (u, v) ->
                    chosenPerEdgeTarget[edgeKey(u, v)] = majorEdgeTargets[edgeKey(u, v)] ?: perHopTargetFallback
                }
                realPickedRps.forEach { rp ->
                    val detourTargets = detourEdgeTargets[rp] ?: return@forEach
                    rp.dropLast(1).zip(rp.drop(1)).forEach { (u, v) ->
                        val k = edgeKey(u, v)
                        chosenPerEdgeTarget[k] = detourTargets[k] ?: chosenPerEdgeTarget[k] ?: perHopTargetFallback
                    }
                }

                // Runtime purification on the chosen path
                maybePurifyAlongPath(chosenPath, chosenPerEdgeTarget, perHopTargetFallback)

                // swaps along chosen path
                chosenPath
                    .dropLast(2)
                    .zip(chosenPath.drop(1).dropLast(1))
                    .zip(chosenPath.drop(2))
                    .forEach { (n12, next) ->
                        val (prev, n) = n12

                        val prevLinks = n.links
                            .filter { link ->
                                link.entangled && !link.swappedAt(n) && link.contains(prev) && !link.utilized
                            }
                            .sortedByDescending { link -> link.fidelity }
                            .take(1)
                        val nextLinks = n.links
                            .filter { link ->
                                link.entangled && !link.swappedAt(n) && link.contains(next) && !link.utilized
                            }
                            .sortedByDescending { link -> link.fidelity }
                            .take(1)

                        prevLinks.zip(nextLinks).forEach { (l1, l2) ->
                            n.attemptSwapping(l1, l2)
                        }
                    }
            }

            val deliveredFids: List<Double> = if (majorPath.size > 2) {
                val afterFids = topo.getEstablishedEntanglementFidelities(src, dst)
                newFidelitiesOnly(oldFids, afterFids)
            } else {
                val SDlinks = src.links
                    .filter { link ->
                        link.entangled &&
                            !link.swappedAt(src) &&
                            link.contains(dst) &&
                            !link.utilized
                    }
                    .sortedByDescending { it.fidelity }
                if (SDlinks.isNotEmpty()) {
                    val succDirect = SDlinks.size.coerceAtMost(width)
                    val used = SDlinks.take(succDirect)
                    used.forEach { it.utilize() }
                    used.map { it.fidelity }
                } else emptyList()
            }

            /**
            * end-to-end purification
            * repeatedly take the 2 worst (still-unqualified) pairs, BBPSSW-purify them, keep output on success.
            */
            fun purifyEndToEndPool(poolIn: List<Double>, fth: Double): List<Double> {
            val pool = poolIn.toMutableList()
            while (true) {
                if (pool.size < 2) break
                pool.sortDescending()

                val firstUnqualified = pool.indexOfFirst { it + 1e-12 < fth }
                if (firstUnqualified == -1) break
                if (pool.size - firstUnqualified < 2) break

                val Fa = pool[firstUnqualified]
                val Fb = pool[firstUnqualified + 1]
                pool.removeAt(firstUnqualified + 1)
                pool.removeAt(firstUnqualified)

                val (Fp, ps) = Fidelity.purifyWernerOnce(Fa, Fb)
                val success = randGen.nextDouble() <= ps
                if (success) pool.add(Fp)
            }
            return pool
            }

            val purifiedPool = purifyEndToEndPool(deliveredFids, FTH)
            val succ = purifiedPool.size
            val estF = if (purifiedPool.isNotEmpty()) purifiedPool.average() else 0.0
            val qualifiedSucc = purifiedPool.count { it + 1e-12 >= FTH }

            logWriter.append(""" ${majorPath.map { it.id }}, $width $succ $estF $qualifiedSucc""").append('\n')

            pathToRecoveryPaths[pathWithWidth].forEach { rpData ->
                val ids = rpData.path.map { node -> node.id }
                logWriter.append(
                    """  $ids, $width ${rpData.available} ${rpData.taken}"""
                ).append('\n')
            }

            logWriter.append('\n')
        }
    }
}
