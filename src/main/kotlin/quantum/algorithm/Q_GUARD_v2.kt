package quantum.algorithm

import quantum.topo.*
import quantum.Fidelity
import quantum.PurificationCostTable
import quantum.tryPurifyOnEdge
import utils.ReducibleLazyEvaluation
import utils.format

class Q_GUARD_v2(
    topo: Topo,
    allowRecoveryPaths: Boolean = true
) : OnlineAlgorithm(topo, allowRecoveryPaths) {

    // label for logs / plot legends
    override val name: String = "QG-v2"

    private val ENABLE_PURIFICATION = true
    private val PUR_DETERMINISTIC = false
    private val C_PUR = 1  // cost unit per attempt

    private val F_TH = 0.7 // hardcoded for now
    
    private val reqFth: MutableMap<Pair<Int,Int>, Double> = mutableMapOf()

    fun setThreshold(srcId: Int, dstId: Int, fth: Double) {
        val key = if (srcId <= dstId) srcId to dstId else dstId to srcId
        reqFth[key] = fth
    }

    private fun fthFor(src: Node, dst: Node): Double {
        val key = if (src.id <= dst.id) src.id to dst.id else dst.id to src.id
        return reqFth[key] ?: defaultFth
    }

    private data class PathExgResult(
        val path: List<Node>,
        val perHopTarget: Double,
        val exg: Double,
        val feasible: Boolean,
        val totalPurCostExg: Int
    )

    private fun computeExgForPath(
        path: List<Node>,
        width: Int,
        fth: Double,
        overrideTargets: Map<Pair<Node, Node>, Double>? = null,
        defaultPerHopTarget: Double? = null
    ): PathExgResult {
        if (path.size < 2 || width <= 0) {
            return PathExgResult(
                path = path,
                perHopTarget = 0.0,
                exg = 0.0,
                feasible = false,
                totalPurCostExg = 0
            )
        }

        val hops = path.size - 1

        // Fallback if caller does not override per-hop targets
        val baseTarget: Double = defaultPerHopTarget ?: Fidelity.perHopTargetF(fth, hops)

        val hopInfo = topo.perHopFreshF(path)
        var totalPurCostExg = 0
        var exgFeasible = true

        val perHopBudget = (width - 1).coerceAtLeast(0)

        var availabilitySum = 0.0
        var availabilityCount = 0

        for ((edge, _, F0) in hopInfo) {
            val u = edge.n1
            val v = edge.n2
            val key = if (u.id <= v.id) Pair(u, v) else Pair(v, u)

            // Either caller-provided edge-specific target, or the common base target
            val targetF = overrideTargets?.get(key) ?: baseTarget

            val rawCost = PurificationCostTable.minCostToReach(F0, targetF)

            // Analytic feasibility
            if (rawCost == Int.MAX_VALUE || rawCost > perHopBudget) {
                exgFeasible = false
                break
            }

            totalPurCostExg += rawCost

            // Rough model: number of raw pairs needed grows ~2^(#rounds)
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
                path = path,
                perHopTarget = baseTarget,
                exg = 0.0,
                feasible = false,
                totalPurCostExg = totalPurCostExg
            )
        }

        val numSwaps = (path.size - 2).coerceAtLeast(0)
        val qPath = Math.pow(topo.q, numSwaps.toDouble())

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
            path = path,
            perHopTarget = baseTarget,
            exg = exg,
            feasible = true,
            totalPurCostExg = totalPurCostExg
        )
    }

    override fun P4() {
        fun newFidelitiesOnly(oldF: List<Double>, newF: List<Double>, scale: Double = 1e12): MutableList<Double> {
        val counts = HashMap<Long, Int>()
        fun key(x: Double): Long = Math.round(x * scale)

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
        majorPaths.forEach { pathWithWidth ->
            var lastSuccessfulPathForLog: List<Node>? = null

            val (_, width, majorPath) = pathWithWidth
            val src = majorPath.first()
            val dst = majorPath.last()
            val oldFids = topo.getEstablishedEntanglementFidelities(src, dst)

            val predF = topo.predictedEndToEndFidelity(majorPath)
            val hops = majorPath.size - 1
            val FTH = fthFor(majorPath.first(), majorPath.last())

            val hopInfoMajor = topo.perHopFreshF(majorPath)
            val hopsMajor = majorPath.dropLast(1).zip(majorPath.drop(1))

            val hopLengths = hopsMajor.map { (u, v) ->
                topo.linksBetween(u, v).firstOrNull()?.l ?: Double.POSITIVE_INFINITY
            }

            val hopTargetsMajor = Fidelity.perHopWeightedTargetsF(FTH, hopLengths)

            // For convenience (logging / defaults), keep an average target
            val perHopTargetMajor: Double =
                if (hopTargetsMajor.isNotEmpty()) hopTargetsMajor.average() else 0.0

            // Map each major-path edge -> its weighted target fidelity
            val perEdgeTargetMajor: MutableMap<Pair<Node, Node>, Double> = mutableMapOf()
            majorPath
                .dropLast(1).zip(majorPath.drop(1))
                .zip(hopTargetsMajor)
                .forEach { (uv, targetF) ->
                    val (u, v) = uv
                    val key = if (u.id <= v.id) Pair(u, v) else Pair(v, u)
                    perEdgeTargetMajor[key] = targetF
                }

            val wTh = Fidelity.wFromF(FTH)

            // Debug: which hops are weak relative to their *own* weighted target
            val weakStr = hopInfoMajor
                .filter { triple ->
                    val edge = triple.first
                    val F0 = triple.third
                    val key = if (edge.n1.id <= edge.n2.id)
                        Pair(edge.n1, edge.n2)
                    else
                        Pair(edge.n2, edge.n1)
                    val target = perEdgeTargetMajor[key] ?: perHopTargetMajor
                    F0 + 1e-12 < target
                }
                .joinToString(prefix = "[", postfix = "]") { triple ->
                    val edge = triple.first
                    val F0 = triple.third
                    "(${edge.n1.id},${edge.n2.id})->${"%.3f".format(F0)}"
                }

            // logWriter.appendln(
            //     "PRED ${majorPath.map { node -> node.id }} " +
            //         "hops=$hops predF=$predF targetHopF=$perHopTargetMajor weak=$weakStr"
            // )

            // For total successes across all width units
            val oldNumOfPairs = topo
                .getEstablishedEntanglements(majorPath.first(), majorPath.last())
                .size

            val recoveryPaths = this.recoveryPaths[pathWithWidth]!!
                .sortedBy { tup -> tup.third.size * 10000 + majorPath.indexOf(tup.third.first()) }

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

            val edges = (0..majorPath.size - 2).zip(1..majorPath.size - 1)
            val rpToWidth = recoveryPaths
                .map { it.third to it.second }
                .toMap()
                .toMutableMap()

            // For each recovery path, remember which major-path segment [s1, s2] it replaces
            val rpToSegmentRange: MutableMap<Path, Pair<Int, Int>> = mutableMapOf()
            recoveryPaths.forEach { (_, _, rp) ->
                val s1 = majorPath.indexOf(rp.first())
                val s2 = majorPath.indexOf(rp.last())
                if (s1 >= 0 && s2 > s1) {
                    rpToSegmentRange[rp] = s1 to s2
                }
            }

            for (i in 1..width) {
                // for w-width major path, treat it as w different paths, and repair separately

                // ===== Q-CAST: find broken edges and candidate recovery paths =====
                val brokenEdges = java.util.LinkedList(
                    edges.filter { (i1, i2) ->
                        val (n1, n2) = majorPath[i1] to majorPath[i2]

                        // Is there at least one usable entangled link on this hop?
                        val hasEntangled = n1.links.any { link ->
                            link.contains(n2) &&
                            link.assigned &&
                            link.notSwapped() &&
                            link.entangled &&
                            !link.utilized
                        }

                        !hasEntangled  // broken if NO entangled link exists
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

                        // --- NEW: segment-local EXG decision: major segment vs this recovery path ---

                        val range = rpToSegmentRange[rp] ?: continue@tryRp
                        val (s1, s2) = range

                        // Major segment nodes from s1..s2 along the major path
                        val majorSeg: List<Node> = majorPath.subList(s1, s2 + 1)

                        // Effective width for the segment: min reserved width and actual width on that segment
                        val widthMajorSegPhase4 = topo.widthPhase4(majorSeg)
                        val widthDetourSegPhase4 = topo.widthPhase4(rp)

                        // Cap by original “nominal” width so we don’t exceed reservation
                        val effectiveWidthMajorSeg = minOf(width, widthMajorSegPhase4)
                        val effectiveWidthDetourSeg = minOf(width, widthDetourSegPhase4)

                        // EXG for the major segment using the global per-hop target
                        val exgMajorSeg = computeExgForPath(
                            majorSeg,
                            effectiveWidthMajorSeg,
                            FTH,
                            overrideTargets = perEdgeTargetMajor,
                            defaultPerHopTarget = null
                        )

                        // Compute a per-hop target for the detour segment by reusing the segment budget
                        val rMajor = s2 - s1          // # hops in the major segment replaced
                        val rDetour = rp.size - 1     // # hops in the detour

                        val wTh = Fidelity.wFromF(FTH)
                        val wSeg = Math.pow(wTh, rMajor.toDouble() / hops.toDouble())
                        val wDetourHop = Math.pow(wSeg, 1.0 / rDetour.toDouble())
                        val fDetourHop = Fidelity.fFromW(wDetourHop)

                        val perEdgeTargetsSeg = mutableMapOf<Pair<Node, Node>, Double>()
                        rp.dropLast(1).zip(rp.drop(1)).forEach { (u, v) ->
                            val key = if (u.id <= v.id) Pair(u, v) else Pair(v, u)
                            perEdgeTargetsSeg[key] = fDetourHop
                        }

                        val exgDetourSeg = computeExgForPath(
                            rp,
                            effectiveWidthDetourSeg,
                            FTH,
                            overrideTargets = perEdgeTargetsSeg,
                            defaultPerHopTarget = perHopTargetMajor
                        )

                        // Only consider this recovery path if it is EXG-feasible and better than the major segment
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
                                // rps overlap; abort this rp
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
                        // this major path cannot be fully repaired for this width unit
                        break
                    }
                }

                // Build the repaired path p using the chosen recovery paths
                val p = realPickedRps.fold(majorPath) { acc, rp ->
                    val pathData = pathToRecoveryPaths[pathWithWidth].first { rpData -> rpData.path == rp }
                    pathData.taken++

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

                // Debug for the repaired path (kept here if you want logging)
                val predFRepaired = topo.predictedEndToEndFidelity(p)
                val perHopTargetNowP = Fidelity.perHopTargetF(FTH, p.size - 1)
                // if (i == 1) {
                //     logWriter.appendln(
                //         "REPAIR-PRED ${p.map { node -> node.id }} hops=${p.size - 1} " +
                //             "predF=${predFRepaired} targetHopF=${perHopTargetNowP}"
                //     )
                // }

                // At this point, realPickedRps contains only those recovery paths that:
                // - are feasible under the local EXG comparison, and
                // - were selected by the Q-CAST coverage logic for this width unit.

                if (realPickedRps.isEmpty() && brokenEdges.isNotEmpty()) {
                    // Nothing could be repaired for this width unit; skip it
                    continue
                }

                // Build the final path for this width unit by splicing the chosen detours into the major path
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

                lastSuccessfulPathForLog = chosenPath

                // Build per-edge target fidelity for this chosen path, using
                // distance-weighted per-hop targets along the path.
                val chosenPerEdgeTarget: MutableMap<Pair<Node, Node>, Double> = mutableMapOf()

                // 1) Detour hops: recompute the detour per-hop target the same way as in the EXG comparison
                for (rp in realPickedRps) {
                    val range = rpToSegmentRange[rp] ?: continue
                    val (s1, s2) = range

                    val rMajor = s2 - s1       // # hops in the major segment replaced
                    val rDetour = rp.size - 1  // # hops in the detour

                    val wTh = Fidelity.wFromF(FTH)
                    val wSeg = Math.pow(wTh, rMajor.toDouble() / hops.toDouble())
                    val wDetourHop = Math.pow(wSeg, 1.0 / rDetour.toDouble())
                    val fDetourHop = Fidelity.fFromW(wDetourHop)

                    rp.dropLast(1).zip(rp.drop(1)).forEach { (u, v) ->
                        val key = if (u.id <= v.id) Pair(u, v) else Pair(v, u)
                        chosenPerEdgeTarget[key] = fDetourHop
                    }
                }

                // 2) Remaining major-path hops: use the weighted major-path target for that edge
                chosenPath
                    .dropLast(1).zip(chosenPath.drop(1))
                    .forEach { (u, v) ->
                        val key = if (u.id <= v.id) Pair(u, v) else Pair(v, u)
                        val majorTarget = perEdgeTargetMajor[key] ?: perHopTargetMajor
                        chosenPerEdgeTarget.putIfAbsent(key, majorTarget)
                    }

                // ===== Runtime purification only on the chosenPath =====
                var totalPurCostOnChosen = 0

                if (ENABLE_PURIFICATION) {
                    val hopsOnChosen = chosenPath.dropLast(1).zip(chosenPath.drop(1))

                    for ((u, v) in hopsOnChosen) {
                        // Local target for this specific hop (u,v)
                        val key = if (u.id <= v.id) Pair(u, v) else Pair(v, u)
                        val targetF = chosenPerEdgeTarget[key] ?: perHopTargetMajor

                        while (true) {
                            val pool = topo.linksBetween(u, v)
                                .filter { it.entangled && it.notSwapped() && !it.utilized }

                            val bestLink: Link? = pool.maxBy { link -> link.fidelity }
                            val bestF = bestLink?.fidelity ?: 0.0

                            if (pool.size < 2) break
                            if (bestF + 1e-12 >= targetF) break

                            val purifyResult = tryPurifyOnEdge(
                                topo,
                                u, v,
                                targetF,
                                PUR_DETERMINISTIC,
                                C_PUR
                            )

                            totalPurCostOnChosen += purifyResult.costUnits
                        }
                    }

                    // if (totalPurCostOnChosen > 0) {
                    //     logWriter.appendln(
                    //         " EXG-PATH ${chosenPath.map { node -> node.id }} " +
                    //             "widthUnit=$i CpurRuntime=$totalPurCostOnChosen"
                    //     )
                    // }
                }

                // GATE: check if each hop can meet its *local* per-hop target with its best available pair
                var allHopsMeetTarget = true
                val hopsOnChosen = chosenPath.dropLast(1).zip(chosenPath.drop(1))

                for ((u, v) in hopsOnChosen) {
                    val key = if (u.id <= v.id) Pair(u, v) else Pair(v, u)
                    val targetF = chosenPerEdgeTarget[key] ?: perHopTargetMajor

                    val pool = topo.linksBetween(u, v)
                        .filter { it.entangled && it.notSwapped() && !it.utilized }

                    val bestF = pool.maxBy { link -> link.fidelity }?.fidelity ?: 0.0

                    if (bestF + 1e-12 < targetF) {
                        allHopsMeetTarget = false
                        break
                    }
                }

                if (!allHopsMeetTarget) {
                    continue  // skip swaps for this width unit
                }

                // ===== Swaps only along the chosenPath (same pattern as before) =====
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
                            l1.utilize()
                            if (next == chosenPath.last()) {
                                l2.utilize()
                            }
                        }
                    }
            }

            val deliveredFids: List<Double> = if (majorPath.size > 2) {
            val afterFids = topo.getEstablishedEntanglementFidelities(src, dst)
            newFidelitiesOnly(oldFids, afterFids)
            } else {
            // 1-hop: fidelity is per delivered direct link
            val SDlinks = src.links
                .filter { link ->
                link.entangled &&
                !link.swappedAt(src) &&
                link.contains(dst) &&
                !link.utilized
                }
                .sortedByDescending { it.fidelity } // optional: take best direct pairs
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

            logWriter.appendln(""" ${majorPath.map { it.id }}, $width $succ $estF $qualifiedSucc""")

            val avgF = estF
            val succAboveFth = qualifiedSucc

            val pathIds = majorPath.map { it.id }
            // logWriter.appendln(
            //     " [${pathIds.joinToString(", ")}], $width $succ " +
            //     "// avgF=${avgF.format(4)} succAboveFth=$succAboveFth"
            // )

            pathToRecoveryPaths[pathWithWidth].forEach { rpData ->
                val ids = rpData.path.map { node -> node.id }
                logWriter.appendln(
                    """  $ids, $width ${rpData.available} ${rpData.taken}"""
                )
            }

            logWriter.appendln()
        }
    }
}