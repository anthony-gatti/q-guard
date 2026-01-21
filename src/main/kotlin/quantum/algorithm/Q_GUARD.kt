package quantum.algorithm

import quantum.topo.*
import quantum.Fidelity
import quantum.PurificationCostTable
import quantum.tryPurifyOnEdge
import utils.ReducibleLazyEvaluation
import kotlin.math.pow
import kotlin.math.roundToLong

open class Q_GUARD(
    topo: Topo,
    allowRecoveryPaths: Boolean = true
) : OnlineAlgorithm(topo, allowRecoveryPaths) {

    // label for logs / plot legends
    override val name: String = "QG"

    private val ENABLE_PURIFICATION = true
    private val PUR_DETERMINISTIC = false
    private val C_PUR = 1  // cost unit per attempt
    
    private val reqFth: MutableMap<Pair<Int,Int>, Double> = mutableMapOf()

    fun setThreshold(srcId: Int, dstId: Int, fth: Double) {
        val key = if (srcId <= dstId) srcId to dstId else dstId to srcId
        reqFth[key] = fth
    }

    private fun edgeKey(u: Node, v: Node): Pair<Int, Int> {
        val a = u.id
        val b = v.id
        return if (a <= b) a to b else b to a
    }

    protected fun fthFor(src: Node, dst: Node): Double {
        val key = if (src.id <= dst.id) src.id to dst.id else dst.id to src.id
        return reqFth[key] ?: defaultFth
    }

    private data class PathExgResult(
        val exg: Double,
        val feasible: Boolean,
    )

    // computes exg for a given path
    private fun computeExgForPath(
        path: List<Node>,
        width: Int,
        fth: Double,
        overrideTargets: Map<Pair<Int, Int>, Double>? = null,
        defaultPerHopTarget: Double? = null
    ): PathExgResult {
        if (path.size < 2 || width <= 0) {
            return PathExgResult(
                exg = 0.0,
                feasible = false,
            )
        }

        val hops = path.size - 1
        val perHopTargetDefault =
            defaultPerHopTarget ?: Fidelity.perHopTargetF(fth, hops)

        val hopInfo = topo.perHopFreshF(path)
        var totalPurCostExg = 0
        var exgFeasible = true

        val perHopBudget = (width - 1).coerceAtLeast(0)

        var availabilitySum = 0.0
        var availabilityCount = 0

        for ((edge, _, F0) in hopInfo) {
            val u = edge.n1
            val v = edge.n2
            val key = edgeKey(u, v)

            val targetF = overrideTargets?.get(key) ?: perHopTargetDefault

            val rawCost = PurificationCostTable.minCostToReach(F0, targetF)
            // Analytic feasibility
            if (rawCost == Int.MAX_VALUE || rawCost > perHopBudget) {
                exgFeasible = false
                break
            }

            totalPurCostExg += rawCost

            // Realized availability on this hop
            val requiredPairs =
                if (rawCost <= 0) 1 else (1 shl rawCost).coerceAtMost(1 shl 30)

            val availablePairs = topo.linksBetween(u, v)
                .count { link ->
                    link.entangled && link.notSwapped() && !link.utilized
                }

            val ratio =
                if (requiredPairs > 0)
                    (availablePairs.toDouble() / requiredPairs.toDouble())
                        .coerceIn(0.0, 1.0)
                else
                    1.0

            availabilitySum += ratio
            availabilityCount += 1
        }

        if (!exgFeasible) {
            return PathExgResult(
                exg = 0.0,
                feasible = false,
            )
        }

        val numSwaps = (path.size - 2).coerceAtLeast(0)
        val qPath = topo.q.pow(numSwaps.toDouble())

        val baseExg = run {
            val num = width.toDouble() * qPath
            val denom = 1.0 + totalPurCostExg.toDouble()
            if (denom > 0.0) num / denom else 0.0
        }

        val availabilityFactor =
            if (availabilityCount > 0)
                (availabilitySum / availabilityCount).coerceIn(0.0, 1.0)
            else
                1.0

        val exg = baseExg * availabilityFactor

        return PathExgResult(
            exg = exg,
            feasible = true,
        )
    }

    // computes a uniform per-hop fidelity target for each detour of each recovery path
    private fun computeDetourPerHopTargets(
        recoveryPaths: List<PickedPath>,
        rpToSegmentRange: Map<Path, Pair<Int, Int>>,
        wTh: Double,
        majorHops: Int
    ): Map<Path, Double> {
        val detourPerHopTarget = mutableMapOf<Path, Double>()

        for ((_, _, detourPath) in recoveryPaths) {
            val segRange = rpToSegmentRange[detourPath] ?: continue
            val (iStart, iEnd) = segRange

            val rMajor = iEnd - iStart
            val rDetour = detourPath.size - 1

            val wSeg = wTh.pow(rMajor.toDouble() / majorHops.toDouble())
            val wDetourHop = wSeg.pow(1.0 / rDetour.toDouble())
            detourPerHopTarget[detourPath] = Fidelity.fFromW(wDetourHop)
        }

        return detourPerHopTarget
    }

    // returns fidelities that are in newF but not oldF
    private fun newFidelitiesOnly(
        oldF: List<Double>,
        newF: List<Double>,
        scale: Double = 1e12
    ): MutableList<Double> {
        val counts = HashMap<Long, Int>()
        fun key(x: Double): Long = (x * scale).roundToLong()

        oldF.forEach { f ->
            val k = key(f)
            counts[k] = (counts[k] ?: 0) + 1
        }

        val out = mutableListOf<Double>()
        newF.forEach { f ->
            val k = key(f)
            val c = counts[k] ?: 0
            if (c > 0) counts[k] = c - 1 else out.add(f)
        }
        return out
    }

    // Build per-edge purification targets for a given path
    private fun buildChosenPerEdgeTargets(
        chosenPath: List<Node>,
        pickedRps: Set<Path>,
        detourPerHopTarget: Map<Path, Double>,
        perHopTargetMajor: Double
    ): MutableMap<Pair<Int, Int>, Double> {
        val targets = mutableMapOf<Pair<Int, Int>, Double>()

        // Detour hops
        for (rp in pickedRps) {
            val fDetourHop = detourPerHopTarget[rp] ?: perHopTargetMajor
            rp.dropLast(1).zip(rp.drop(1)).forEach { (u, v) ->
                targets[edgeKey(u, v)] = fDetourHop
            }
        }

        // Remaining hops on chosenPath
        chosenPath.dropLast(1).zip(chosenPath.drop(1)).forEach { (u, v) ->
            targets.putIfAbsent(edgeKey(u, v), perHopTargetMajor)
        }

        return targets
    }

    // Purification along chosen path
    // keep purifying until fewer than 2 entg pairs remain, or best available pair meets target fid
    private fun maybePurifyAlongPath(
        chosenPath: List<Node>,
        chosenPerEdgeTarget: Map<Pair<Int, Int>, Double>,
        perHopTargetMajor: Double
    ) {
        if (!ENABLE_PURIFICATION) return

        val hopsOnChosen = chosenPath.dropLast(1).zip(chosenPath.drop(1))
        for ((u, v) in hopsOnChosen) {
            val targetF = chosenPerEdgeTarget[edgeKey(u, v)] ?: perHopTargetMajor

            while (true) {
                val pool = topo.linksBetween(u, v)
                    .filter { it.entangled && it.notSwapped() && !it.utilized }

                val bestF = pool.maxBy { it.fidelity }?.fidelity ?: 0.0

                if (pool.size < 2) break
                if (bestF + 1e-12 >= targetF) break

                tryPurifyOnEdge(topo, u, v, targetF, PUR_DETERMINISTIC, C_PUR)
            }
        }
    }

    // ensure all hops on chosen path have at least one pair that meets target
    private fun allHopsMeetTargets(
        chosenPath: List<Node>,
        chosenPerEdgeTarget: Map<Pair<Int, Int>, Double>,
        perHopTargetMajor: Double
    ): Boolean {
        for ((u, v) in chosenPath.dropLast(1).zip(chosenPath.drop(1))) {
            val targetF = chosenPerEdgeTarget[edgeKey(u, v)] ?: perHopTargetMajor

            val bestF = topo.linksBetween(u, v)
                .filter { it.entangled && it.notSwapped() && !it.utilized }
                .maxBy { it.fidelity }
                ?.fidelity ?: 0.0

            if (bestF + 1e-12 < targetF) return false
        }
        return true
    }

    // Recovery + swapping + purification stage
    override fun P4() {
        majorPaths.forEach { pathWithWidth ->
            val (_, width, majorPath) = pathWithWidth
            val src = majorPath.first()
            val dst = majorPath.last()
            val oldFids = topo.getEstablishedEntanglementFidelities(src, dst)

            val hops = majorPath.size - 1
            val FTH = fthFor(majorPath.first(), majorPath.last())
            val perHopTargetMajor = Fidelity.perHopTargetF(FTH, hops)

            val wTh = Fidelity.wFromF(FTH)

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

            val detourPerHopTarget = computeDetourPerHopTargets(recoveryPaths, rpToSegmentRange, wTh, hops)

            val edges = (0..majorPath.size - 2).zip(1..majorPath.size - 1)
            val rpToWidth = recoveryPaths
                .map { it.third to it.second }
                .toMap()
                .toMutableMap()

            for (i in 1..width) {
                // for w-width major path, treat it as w different paths, and repair separately
                // find broken edges and candidate recovery paths
                val brokenEdges = java.util.LinkedList(
                    edges.filter { (i1, i2) ->
                        val (n1, n2) = majorPath[i1] to majorPath[i2]

                        // check for any entangled links on the hop
                        val hasEntangled = n1.links.any { link ->
                            link.contains(n2) &&
                            link.assigned &&
                            link.notSwapped() &&
                            link.entangled &&
                            !link.utilized
                        }

                        !hasEntangled  // broken if no entangled link exists
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
                    if (realRepairedEdges.contains(brokenEdge)) continue  // already repaired

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

                        // segment-local EXG decision
                        val range = rpToSegmentRange[rp] ?: continue@tryRp
                        val (s1, s2) = range

                        // Major segment nodes from s1..s2 along the major path
                        val majorSeg: List<Node> = majorPath.subList(s1, s2 + 1)

                        // Effective width for the segment
                        val widthMajorSeg = topo.widthPhase4(majorSeg)
                        val widthDetourSeg = topo.widthPhase4(rp)

                        // Cap by original width
                        val effectiveWidthMajorSeg = minOf(width, widthMajorSeg)
                        val effectiveWidthDetourSeg = minOf(width, widthDetourSeg)

                        // Compute EXG for the major segment using the global per-hop target
                        val exgMajorSeg = computeExgForPath(
                            majorSeg,
                            effectiveWidthMajorSeg,
                            FTH,
                            overrideTargets = null,
                            defaultPerHopTarget = perHopTargetMajor
                        )

                        // Compute EXG for the detour segment using its segment-specific per-hop target
                        val perEdgeTargetsSeg = mutableMapOf<Pair<Int, Int>, Double>()
                        val fDetourHop = detourPerHopTarget[rp] ?: perHopTargetMajor

                        rp.dropLast(1).zip(rp.drop(1)).forEach { (u, v) ->
                            val key = edgeKey(u, v)
                            perEdgeTargetsSeg[key] = fDetourHop
                        }

                        val exgDetourSeg = computeExgForPath(
                            rp,
                            effectiveWidthDetourSeg,
                            FTH,
                            overrideTargets = perEdgeTargetsSeg,
                            defaultPerHopTarget = perHopTargetMajor
                        )

                        // Only consider recovery path if it is EXG-feasible and better than the major segment
                        if (!exgDetourSeg.feasible || exgDetourSeg.exg <= exgMajorSeg.exg) {
                            continue@tryRp
                        }

                        val pickedRps = realPickedRps.toHashSet()
                        val repairedEdges = realRepairedEdges.toHashSet()

                        val otherCoveredEdges =
                            rpToEdges[rp]!!.toHashSet() - brokenEdge

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
                        // major path cannot be fully repaired for this width unit
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

                val chosenPerEdgeTarget = buildChosenPerEdgeTargets(
                    chosenPath = chosenPath,
                    pickedRps = realPickedRps,
                    detourPerHopTarget = detourPerHopTarget,
                    perHopTargetMajor = perHopTargetMajor
                )

                // Runtime purification on the chosen path
                maybePurifyAlongPath(chosenPath, chosenPerEdgeTarget, perHopTargetMajor)

                if (!allHopsMeetTargets(chosenPath, chosenPerEdgeTarget, perHopTargetMajor)) continue

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
                .sortedByDescending { it.fidelity } // take best direct pairs
            if (SDlinks.isNotEmpty()) {
                val succDirect = SDlinks.size.coerceAtMost(width)
                val used = SDlinks.take(succDirect)
                used.forEach { it.utilize() }
                used.map { it.fidelity }
            } else emptyList()
            }

            val succ = deliveredFids.size
            val estF = if (deliveredFids.isNotEmpty()) deliveredFids.average() else 0.0
            val qualifiedSucc = deliveredFids.count { it + 1e-12 >= FTH }

            logWriter.appendLine(""" ${majorPath.map { it.id }}, $width $succ $estF $qualifiedSucc""")

            val avgF = estF
            val succAboveFth = qualifiedSucc

            val pathIds = majorPath.map { it.id }

            pathToRecoveryPaths[pathWithWidth].forEach { rpData ->
                val ids = rpData.path.map { node -> node.id }
                logWriter.appendLine(
                    """  $ids, $width ${rpData.available} ${rpData.taken}"""
                )
            }

            logWriter.appendLine()
        }
    }
}