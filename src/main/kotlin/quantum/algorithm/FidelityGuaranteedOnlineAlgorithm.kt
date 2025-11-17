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
    override val name: String = "TEMP-NAME-QCAST"

    private val ENABLE_PURIFICATION = true
    private val PUR_DETERMINISTIC = false
    private val C_PUR = 1  // cost unit per attempt

    private val F_TH = 0.8 // hardcoded for now
    
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
        fth: Double
    ): PathExgResult {
        if (path.size < 2) {
            return PathExgResult(path, 0.0, 0.0, false, Int.MAX_VALUE)
        }

        val hops = path.size - 1
        val perHopTarget = Fidelity.perHopTargetF(fth, hops)

        val hopInfo = topo.perHopFreshF(path)  // (edge, tau, F0)
        val perHopBudget = (width - 1).coerceAtLeast(0)

        var totalPurCostExg = 0
        var exgFeasible = true

        for ((_, _, F0) in hopInfo) {
            val rawCost = PurificationCostTable.minCostToReach(F0, perHopTarget)

            val hopFeasible = rawCost != Int.MAX_VALUE && rawCost <= perHopBudget
            if (!hopFeasible) {
                exgFeasible = false
                // you can early-return here if you want to short-circuit
            } else {
                totalPurCostExg += rawCost
            }
        }

        val qPath = Math.pow(topo.q, (path.size - 2).coerceAtLeast(0).toDouble())
        val exg = if (exgFeasible) {
            val num = width * qPath
            val denom = 1.0 + totalPurCostExg.toDouble()
            if (denom > 0.0) num / denom else 0.0
        } else {
            0.0
        }

        return PathExgResult(path, perHopTarget, exg, exgFeasible, totalPurCostExg)
    }

    override fun P4() {
        majorPaths.forEach { pathWithWidth ->
            var lastSuccessfulPathForLog: List<Node>? = null

            val (_, width, majorPath) = pathWithWidth

            val predF = topo.predictedEndToEndFidelity(majorPath)
            val hops = majorPath.size - 1
            val FTH = fthFor(majorPath.first(), majorPath.last())
            val perHopTarget = Fidelity.perHopTargetF(FTH, hops)

            // Debug: which hops are weak on the *fresh* link fidelity
            val hopInfoMajor = topo.perHopFreshF(majorPath)
            val weakStr = hopInfoMajor
                .filter { triple -> triple.third + 1e-12 < perHopTarget }
                .joinToString(prefix = "[", postfix = "]") { triple ->
                    val edge = triple.first
                    val F0 = triple.third
                    "(${edge.n1.id},${edge.n2.id})->${"%.3f".format(F0)}"
                }

            logWriter.appendln(
                "PRED ${majorPath.map { node -> node.id }} " +
                    "hops=$hops predF=$predF targetHopF=$perHopTarget weak=$weakStr"
            )

            // For total successes across all width units
            val oldNumOfPairs = topo
                .getEstablishedEntanglements(majorPath.first(), majorPath.last())
                .size

            val recoveryPaths = this.recoveryPaths[pathWithWidth]!!
                .sortedBy { tup -> tup.third.size * 10000 + majorPath.indexOf(tup.third.first()) }

            recoveryPaths.forEach { (src, w, p) ->
                val available = p.edges()
                    .map { (n1, n2) -> n1.links.count { link -> link.contains(n2) && link.entangled } }
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
                    var next = 0

                    tryRp@ for (rp in edgeToRps[brokenEdge]!!
                        .filter { rpCandidate -> rpToWidth[rpCandidate]!! > 0 && rpCandidate !in realPickedRps }
                        .sortedBy { rpCandidate ->
                            majorPath.indexOf(rpCandidate.first()) * 10000 +
                                majorPath.indexOf(rpCandidate.last())
                        }) {

                        if (majorPath.indexOf(rp.first()) < next) continue
                        next = majorPath.indexOf(rp.last())

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

                    topo.shortestPath(
                        edgesOfNewPathAndCycles,
                        acc.first(),
                        acc.last(),
                        ReducibleLazyEvaluation({ 1.0 })
                    ).second
                }

                // Debug for the repaired path as before
                val predFRepaired = topo.predictedEndToEndFidelity(p)
                val perHopTargetNowP = Fidelity.perHopTargetF(FTH, p.size - 1)
                // if (i == 1) {
                //     logWriter.appendln(
                //         "REPAIR-PRED ${p.map { node -> node.id }} hops=${p.size - 1} " +
                //             "predF=${predFRepaired} targetHopF=${perHopTargetNowP}"
                //     )
                // }

                // ===== NEW: EXG-based choice between majorPath and repaired path =====
                val exgMajor = computeExgForPath(majorPath, width, FTH)
                val exgRepaired = computeExgForPath(p, width, FTH)

                val feasibleCandidates = listOf(exgMajor, exgRepaired).filter { res -> res.feasible }
                val best: PathExgResult? = if (feasibleCandidates.isEmpty()) {
                    null
                } else {
                    feasibleCandidates.maxBy { res -> res.exg }
                }

                if (best == null) {
                    // No EXG-feasible span for this width unit → skip swaps entirely
                    logWriter.appendln(
                        " EXG-SKIP ${majorPath.map { node -> node.id }} widthUnit=$i " +
                            "reason=no_feasible_span " +
                            "EXGmajor=${exgMajor.exg.format(4)} " +
                            "EXGrepaired=${exgRepaired.exg.format(4)}"
                    )
                    continue
                }

                val chosenPath = best.path
                val perHopTargetNow = best.perHopTarget

                if (i == 1) {
                    logWriter.appendln(
                    " EXG-CHOSEN path=${chosenPath.map { node -> node.id }} widthUnit=$i " +
                        "EXGmajor=${exgMajor.exg.format(4)} " +
                        "EXGrepaired=${exgRepaired.exg.format(4)} " +
                        "EXGchosen=${best.exg.format(4)}"
                    )
                }

                // Update for later fidelity logging
                lastSuccessfulPathForLog = chosenPath

                // ===== Runtime purification only on the chosenPath =====
                var totalPurCostOnChosen = 0

                if (ENABLE_PURIFICATION) {
                    val hopsOnChosen = chosenPath.dropLast(1).zip(chosenPath.drop(1))

                    for ((u, v) in hopsOnChosen) {
                        while (true) {
                            val pool = topo.linksBetween(u, v)
                                .filter { link -> link.entangled && link.notSwapped() && !link.utilized }

                            val bestF = pool.maxBy { link -> link.fidelity }?.fidelity ?: 0.0

                            // stop if fewer than 2 pairs, or we've already reached the local target
                            if (pool.size < 2) break
                            if (bestF + 1e-12 >= perHopTargetNow) break

                            val res = tryPurifyOnEdge(
                                topo,
                                u, v,
                                perHopTargetNow,
                                PUR_DETERMINISTIC,
                                C_PUR
                            )

                            totalPurCostOnChosen += res.costUnits

                            logWriter.appendln(
                                " PUR-LOCAL (${u.id},${v.id}) " +
                                    "target=${perHopTargetNow.format(3)} " +
                                    "Fbefore=${res.Fbefore.format(3)} " +
                                    "Fafter=${res.Fafter.format(3)} " +
                                    "attempts=${res.attempts} pairsConsumed=${res.pairsConsumed} " +
                                    "cost=${res.costUnits} " +
                                    "success=${res.success}"
                            )
                        }
                    }
                }

                if (totalPurCostOnChosen > 0) {
                    logWriter.appendln(
                        " EXG-PATH ${chosenPath.map { node -> node.id }} " +
                            "widthUnit=$i CpurRuntime=$totalPurCostOnChosen"
                    )
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

            logWriter.appendln(
                """ ${majorPath.map { node -> node.id }}, $width $succ $estF $qualifiedSucc"""
            )

            // pathToRecoveryPaths[pathWithWidth].forEach { rpData ->
            //     val ids = rpData.path.map { node -> node.id }
            //     logWriter.appendln(
            //         """  $ids, $width ${rpData.available} ${rpData.taken}"""
            //     )
            // }
        }

        logWriter.appendln()
    }
}