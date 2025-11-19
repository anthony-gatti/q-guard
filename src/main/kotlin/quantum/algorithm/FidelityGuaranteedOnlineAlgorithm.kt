package quantum.algorithm

import quantum.topo.*
import quantum.Fidelity
import quantum.PurificationCostTable
import quantum.tryPurifyOnEdge
import utils.ReducibleLazyEvaluation
import utils.format

class FidelityGuaranteedOnlineAlgorithm(
    topo: Topo,
    allowRecoveryPaths: Boolean = true
) : OnlineAlgorithm(topo, allowRecoveryPaths) {

    // label for logs / plot legends
    override val name: String = "FG"

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
        return reqFth[key] ?: F_TH  // fallback to your current global default
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
        val perHopTargetDefault = defaultPerHopTarget ?: Fidelity.perHopTargetF(fth, hops)

        val hopInfo = topo.perHopFreshF(path) // List<Triple<Edge, Double, Double>>
        var totalPurCostExg = 0
        var exgFeasible = true

        val perHopBudget = (width - 1).coerceAtLeast(0)

        for ((edge, _, F0) in hopInfo) {
            val u = edge.n1
            val v = edge.n2
            val key = if (u.id <= v.id) Pair(u, v) else Pair(v, u)

            val targetF = overrideTargets?.get(key) ?: perHopTargetDefault

            val rawCost = PurificationCostTable.minCostToReach(F0, targetF)

            if (rawCost == Int.MAX_VALUE || rawCost > perHopBudget) {
                exgFeasible = false
            } else {
                totalPurCostExg += rawCost
            }
        }

        val numSwaps = (path.size - 2).coerceAtLeast(0)
        val qPath = Math.pow(topo.q, numSwaps.toDouble())

        val exg = if (exgFeasible) {
            val num = width.toDouble() * qPath
            val denom = 1.0 + totalPurCostExg.toDouble()
            if (denom > 0.0) num / denom else 0.0
        } else {
            0.0
        }

        return PathExgResult(
            path = path,
            perHopTarget = perHopTargetDefault,
            exg = exg,
            feasible = exgFeasible,
            totalPurCostExg = totalPurCostExg
        )
    }

    override fun P4() {
        majorPaths.forEach { pathWithWidth ->
            var lastSuccessfulPathForLog: List<Node>? = null

            val (_, width, majorPath) = pathWithWidth

            val predF = topo.predictedEndToEndFidelity(majorPath)
            val hops = majorPath.size - 1
            val FTH = fthFor(majorPath.first(), majorPath.last())
            val perHopTargetMajor = Fidelity.perHopTargetF(FTH, hops)

            val wTh = Fidelity.wFromF(FTH)

            // Debug: which hops are weak on the *fresh* link fidelity
            val hopInfoMajor = topo.perHopFreshF(majorPath)
            val weakStr = hopInfoMajor
                .filter { triple -> triple.third + 1e-12 < perHopTargetMajor }
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

            // === Segment budgets: detour per-hop targets ===
            val detourPerHopTarget: MutableMap<Path, Double> = mutableMapOf()

            recoveryPaths.forEach { (_, _, rp) ->
                val s1 = majorPath.indexOf(rp.first())
                val s2 = majorPath.indexOf(rp.last())

                val rMajor = s2 - s1           // # hops in the major segment replaced
                val rDetour = rp.size - 1      // # hops in the detour

                if (rMajor <= 0 || rDetour <= 0) return@forEach

                // Segment budget in Werner: w_seg = w_th^(rMajor / L)
                val wSeg = Math.pow(wTh, rMajor.toDouble() / hops.toDouble())

                // Per-hop Werner target for the detour: w_detour = w_seg^(1 / rDetour)
                val wDetourHop = Math.pow(wSeg, 1.0 / rDetour.toDouble())

                // Convert back to fidelity
                val fDetourHop = Fidelity.fFromW(wDetourHop)

                detourPerHopTarget[rp] = fDetourHop
            }

            val edges = (0..majorPath.size - 2).zip(1..majorPath.size - 1)
            val rpToWidth = recoveryPaths
                .map { it.third to it.second }
                .toMap()
                .toMutableMap()

            for (i in 1..width) {
                // for w-width major path, treat it as w different paths, and repair separately

                // ===== Q-CAST: find broken edges and candidate recovery paths =====
                val brokenEdges = java.util.LinkedList(
                    edges.filter { (i1, i2) ->
                        val (n1, n2) = majorPath[i1] to majorPath[i2]
                        n1.links.any { link ->
                            link.contains(n2) && link.assigned && link.notSwapped() && !link.entangled
                        }
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

                // Actual available width in Phase 4 based on successful entanglement
                val widthMajorPhase4 = topo.widthPhase4(majorPath)
                val widthRepairedPhase4 = topo.widthPhase4(p)

                // cap by original “nominal” width so path reservation isnt exceeded
                val effectiveWidthMajor = minOf(width, widthMajorPhase4)
                val effectiveWidthRepaired = minOf(width, widthRepairedPhase4)

                // EXG-based choice between majorPath and repaired path
                val exgMajor = computeExgForPath(
                    majorPath,
                    effectiveWidthMajor,
                    FTH,
                    overrideTargets = null,
                    defaultPerHopTarget = perHopTargetMajor
                )
                // Build per-edge targets for the repaired path
                val perEdgeTargets = mutableMapOf<Pair<Node, Node>, Double>()

                // 1) Detour edges: use fDetourHop for each chosen recovery path
                for (rp in realPickedRps) {
                    val fDetourHop = detourPerHopTarget[rp] ?: perHopTargetMajor
                    rp.zipWithNext { u, v ->
                        val key = if (u.id <= v.id) Pair(u, v) else Pair(v, u)
                        perEdgeTargets[key] = fDetourHop
                    }
                }


                // 2) Remaining hops on the major path: use perHopTargetMajor
                majorPath.zipWithNext { u, v ->
                    val key = if (u.id <= v.id) Pair(u, v) else Pair(v, u)
                    if (key !in perEdgeTargets) {
                        perEdgeTargets[key] = perHopTargetMajor
                    }
                }

                val exgRepaired = computeExgForPath(
                    p,
                    effectiveWidthRepaired,
                    FTH,
                    overrideTargets = perEdgeTargets,
                    defaultPerHopTarget = perHopTargetMajor
                )

                val feasibleCandidates = listOf(exgMajor, exgRepaired).filter { res -> res.feasible }

                val best: PathExgResult? = if (feasibleCandidates.isEmpty()) {
                    null
                } else {
                    var bestLocal = feasibleCandidates[0]
                    for (j in 1 until feasibleCandidates.size) {
                        val cand = feasibleCandidates[j]
                        if (cand.exg > bestLocal.exg) {
                            bestLocal = cand
                        }
                    }
                    bestLocal
                }

                if (best == null) {
                    // No EXG-feasible span for this width unit → skip swaps entirely
                    // logWriter.appendln(
                    //     " EXG-SKIP ${majorPath.map { node -> node.id }} widthUnit=$i " +
                    //         "reason=no_feasible_span " +
                    //         "EXGmajor=${exgMajor.exg.format(4)} " +
                    //         "EXGrepaired=${exgRepaired.exg.format(4)}"
                    // )
                    continue
                }

                // Path actually used for this width unit
                val chosenPath = best.path
                lastSuccessfulPathForLog = chosenPath

                // === Build per-edge target fidelity for this chosen path ===
                val chosenPerEdgeTarget: MutableMap<Pair<Node, Node>, Double> = mutableMapOf()

                if (chosenPath == majorPath) {
                    // Pure major path: every hop gets the major per-hop target
                    chosenPath
                        .dropLast(1).zip(chosenPath.drop(1))
                        .forEach { (u, v) ->
                            chosenPerEdgeTarget[Pair(u, v)] = perHopTargetMajor
                        }
                } else {
                    // Repaired path: some hops are on detours, some are on major segments.

                    // 1) Fill detour hops with their segment-specific target
                    for (rp in realPickedRps) {
                        val fDetourHop = detourPerHopTarget[rp] ?: perHopTargetMajor

                        rp.edges().forEach { edge ->
                            val u = edge.n1
                            val v = edge.n2
                            chosenPerEdgeTarget[Pair(u, v)] = fDetourHop
                        }
                    }

                    // 2) Any remaining hops on chosenPath (not part of an rp) get the major target
                    chosenPath
                        .dropLast(1).zip(chosenPath.drop(1))
                        .forEach { (u, v) ->
                            chosenPerEdgeTarget.putIfAbsent(Pair(u, v), perHopTargetMajor)
                        }
                }

                if (i == 1) {
                    // logWriter.appendln(
                    //     " EXG-CHOSEN path=${chosenPath.map { node -> node.id }} widthUnit=$i " +
                    //         "EXGmajor=${exgMajor.exg.format(4)} " +
                    //         "EXGrepaired=${exgRepaired.exg.format(4)} " +
                    //         "EXGchosen=${best.exg.format(4)}"
                    // )
                }

                // ===== Runtime purification only on the chosenPath =====
                var totalPurCostOnChosen = 0

                if (ENABLE_PURIFICATION) {
                    val hopsOnChosen = chosenPath.dropLast(1).zip(chosenPath.drop(1))

                    for ((u, v) in hopsOnChosen) {
                        // Local target for this specific hop (u,v)
                        val targetF = chosenPerEdgeTarget[Pair(u, v)] ?: perHopTargetMajor

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
                    val targetF = chosenPerEdgeTarget[Pair(u, v)] ?: perHopTargetMajor

                    val pool = topo.linksBetween(u, v)
                        .filter { it.entangled && it.notSwapped() && !it.utilized }

                    val bestLink: Link? = pool.maxBy { link -> link.fidelity }
                    val bestF = bestLink?.fidelity ?: 0.0

                    if (bestF + 1e-12 < targetF) {
                        allHopsMeetTarget = false
                        break
                    }
                }

                if (!allHopsMeetTarget) {
                    // logWriter.appendln(
                    //     " EXG-GATE-BLOCK path=${chosenPath.map { it.id }} " +
                    //         "reason=hop_below_target"
                    // )
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
                            .sortedBy { link -> link.id }
                            .take(1)
                        val nextLinks = n.links
                            .filter { link ->
                                link.entangled && !link.swappedAt(n) && link.contains(next) && !link.utilized
                            }
                            .sortedBy { link -> link.id }
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

            // === Same success / fidelity logic, now using lastSuccessfulPathForLog ===
            var succ = 0
            if (majorPath.size > 2) {
                succ = topo.getEstablishedEntanglements(
                    majorPath.first(),
                    majorPath.last()
                ).size - oldNumOfPairs
            } else {
                val SDlinks = majorPath.first().links
                    .filter { link ->
                        link.entangled &&
                            !link.swappedAt(majorPath.first()) &&
                            link.contains(majorPath.last()) &&
                            !link.utilized
                    }
                    .sortedBy { link -> link.id }

                if (SDlinks.isNotEmpty()) {
                    succ = SDlinks.size.coerceAtMost(width)
                    (0 until succ).forEach { pid ->
                        SDlinks[pid].utilize()
                    }
                }
            }

            val estF =
                if (succ > 0 && lastSuccessfulPathForLog != null && lastSuccessfulPathForLog!!.size > 1) {
                    topo.pathEndToEndFidelity(lastSuccessfulPathForLog!!)
                } else 0.0

            val qualifiedSucc = if (succ > 0 && estF + 1e-12 >= FTH) succ else 0

            // logWriter.appendln(
            //     """ ${majorPath.map { node -> node.id }}, $width $succ $estF $qualifiedSucc"""
            // )

            val avgF = estF
            val succAboveFth = qualifiedSucc

            val pathIds = majorPath.map { it.id }
            logWriter.appendln(
                " [${pathIds.joinToString(", ")}], $width $succ " +
                "// avgF=${avgF.format(4)} succAboveFth=$succAboveFth"
            )

            // pathToRecoveryPaths[pathWithWidth].forEach { rpData ->
            //     val ids = rpData.path.map { node -> node.id }
            //     logWriter.appendln(
            //         """  $ids, $width ${rpData.available} ${rpData.taken}"""
            //     )
            // }

            logWriter.appendln()
        }
    }
}