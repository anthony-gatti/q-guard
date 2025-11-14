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

    // Same Q-CAST P4 logic, but with fidelity logging / qualification
    override fun P4() {
        majorPaths.forEach { pathWithWidth ->
            var lastSuccessfulPathForLog: List<Node>? = null

            val (_, width, majorPath) = pathWithWidth

            val predF = topo.predictedEndToEndFidelity(majorPath)
            val hops = majorPath.size - 1
            val FTH = fthFor(majorPath.first(), majorPath.last())
            val perHopTarget = Fidelity.perHopTargetF(FTH, hops)

            // (Optional debug) See which hops are below the per-hop target using *fresh* F0
            val hopInfo = topo.perHopFreshF(majorPath)  // you added this earlier in Step 1
            val weak = hopInfo.filter { (_, _, F0) -> F0 + 1e-12 < perHopTarget }
            logWriter.appendln("PRED ${majorPath.map { it.id }} hops=$hops predF=$predF targetHopF=$perHopTarget weak=${weak.map { (e,_,F0)->"(${e.n1.id},${e.n2.id})->${"%.3f".format(F0)}" }}")


            val oldNumOfPairs = topo
                .getEstablishedEntanglements(majorPath.first(), majorPath.last())
                .size

            val recoveryPaths = this.recoveryPaths[pathWithWidth]!!
                .sortedBy { it.third.size * 10000 + majorPath.indexOf(it.third.first()) }

            recoveryPaths.forEach { (_, w, p) ->
                val available = p.edges()
                    .map { (n1, n2) -> n1.links.count { it.contains(n2) && it.entangled } }
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

                // find all broken edges on the major path
                val brokenEdges = java.util.LinkedList(
                    edges.filter { (i1, i2) ->
                        val (n1, n2) = majorPath[i1] to majorPath[i2]
                        n1.links.any {
                            it.contains(n2) && it.assigned && it.notSwapped() && !it.entangled
                        }
                    }
                )

                val edgeToRps = brokenEdges
                    .map { it to mutableListOf<Path>() }
                    .toMap()
                val rpToEdges = recoveryPaths
                    .map { it.third to mutableListOf<Pair<Int, Int>>() }
                    .toMap()

                recoveryPaths.forEach { (_, _, rp) ->  // rp is calculated from P2
                    val (s1, s2) = majorPath.indexOf(rp.first()) to majorPath.indexOf(rp.last())

                    (s1..s2 - 1).zip(s1 + 1..s2)
                        .filter { it in brokenEdges }
                        .forEach {
                            rpToEdges[rp]!!.add(it)
                            edgeToRps[it]!!.add(rp)
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
                        .filter { rpToWidth[it]!! > 0 && it !in realPickedRps }
                        .sortedBy {
                            majorPath.indexOf(it.first()) * 10000 +
                                majorPath.indexOf(it.last())
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

                        (realPickedRps - pickedRps).forEach {
                            rpToWidth[it] = rpToWidth[it]!! + 1
                        }
                        (pickedRps - realPickedRps).forEach {
                            rpToWidth[it] = rpToWidth[it]!! - 1
                        }

                        realPickedRps = pickedRps
                        realRepairedEdges = repairedEdges
                        break
                    }

                    if (!repaired) {
                        // this major path cannot be repaired
                        break
                    }
                }

                val p = realPickedRps.fold(majorPath) { acc, rp ->
                    val pathData = pathToRecoveryPaths[pathWithWidth].first { it.path == rp }
                    pathData.taken++

                    val toAdd = rp.edges()
                    val toDelete = acc
                        .dropWhile { it != rp.first() }
                        .dropLastWhile { it != rp.last() }
                        .edges()

                    val edgesOfNewPathAndCycles = acc.edges().toSet() - toDelete + toAdd

                    topo.shortestPath(
                        edgesOfNewPathAndCycles,
                        acc.first(),
                        acc.last(),
                        ReducibleLazyEvaluation({ 1.0 })
                    ).second
                }

                // --- Re-gate on the repaired path (hop count may have changed) ---
                val predFRepaired = topo.predictedEndToEndFidelity(p)
                val perHopTargetNow = Fidelity.perHopTargetF(FTH, p.size - 1)
                if (i == 1) { // only on the first width unit
                    logWriter.appendln("REPAIR-PRED ${p.map { it.id }} hops=${p.size-1} predF=${predFRepaired} targetHopF=${perHopTargetNow}")
                }

                var totalPurCostOnP = 0

                // === Purification (optional) — local per-hop thresholds ===
                if (ENABLE_PURIFICATION) {
                    val hopsOnP = p.dropLast(1).zip(p.drop(1))

                    for ((u, v) in hopsOnP) {
                        while (true) {
                            val pool = topo.linksBetween(u, v)
                                .filter { it.entangled && it.notSwapped() && !it.utilized }

                            val bestF = pool.maxBy { it.fidelity }?.fidelity ?: 0.0

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

                            totalPurCostOnP += res.costUnits

                            logWriter.appendln(
                                " PUR-LOCAL (${u.id},${v.id}) " +
                                    "target=${perHopTargetNow.format(3)} " +
                                    "Fbefore=${res.Fbefore.format(3)} " +
                                    "Fafter=${res.Fafter.format(3)} " +
                                    "attempts=${res.attempts} pairsConsumed=${res.pairsConsumed} " +
                                    "cost=${res.costUnits} " +
                                    "success=${res.success}"
                            )

                            // If we failed and burned pairs, the next loop iteration will re-check
                            // pool.size and bestF and exit if there's nothing left or threshold hit.
                        }
                    }
                }

                // === Deterministic purification cost for EXG (table-based) ===
                // This uses *fresh* per-hop fidelities from the physical model, not
                // the current entangled pool, and assumes purification always succeeds.
                val hopInfoForExg = topo.perHopFreshF(p)
                val totalPurCostExg = hopInfoForExg.fold(0) { acc, (_, _, F0) ->
                    val cost = PurificationCostTable.minCostToReach(F0, perHopTargetNow)
                    acc + if (cost == Int.MAX_VALUE) 0 else cost
                }

                // Swap success product on this path (q^{#internal nodes})
                val qPath = Math.pow(topo.q, (p.size - 2).coerceAtLeast(0).toDouble())

                // For EXG, we assume purification *can* raise each hop to its target,
                // so feasibility is based on the design, not the current predFRepaired.
                // The deterministic cost comes from totalPurCostExg.
                val exgNumerator = width * qPath
                val exgDenom = 1.0 + totalPurCostExg.toDouble()
                val exg = if (exgDenom > 0) exgNumerator / exgDenom else 0.0

                if (i==1) {
                    logWriter.appendln(
                        " EXG ${p.map { it.id }} " +
                            "predF_raw=${predFRepaired.format(3)} " +
                            "Fth=${FTH.format(3)} " +
                            "width=$width qPath=${qPath.format(3)} " +
                            "CpurRuntime=$totalPurCostOnP CpurEXG=$totalPurCostExg " +
                            "EXG=${exg.format(4)}"
                    )
                }

                lastSuccessfulPathForLog = p

                // same swap logic as OnlineAlgorithm
                p.dropLast(2).zip(p.drop(1).dropLast(1)).zip(p.drop(2)).forEach { (n12, next) ->
                    val (prev, n) = n12

                    val prevLinks = n.links
                        .filter { it.entangled && !it.swappedAt(n) && it.contains(prev) && !it.utilized }
                        .sortedBy { it.id }
                        .take(1)
                    val nextLinks = n.links
                        .filter { it.entangled && !it.swappedAt(n) && it.contains(next) && !it.utilized }
                        .sortedBy { it.id }
                        .take(1)

                    prevLinks.zip(nextLinks).forEach { (l1, l2) ->
                        n.attemptSwapping(l1, l2)
                        l1.utilize()
                        if (next == p.last()) {
                            l2.utilize()
                        }
                    }
                }

                logWriter.appendln(
                    " EXG-PATH ${p.map { it.id }} " +
                    "widthUnit=$i totalPurCost=$totalPurCostOnP"
                )
            }

            // === HERE: identical succ logic, but we add fidelity + qualifiedSucc ===
            var succ = 0
            if (majorPath.size > 2) {
                succ = topo.getEstablishedEntanglements(
                    majorPath.first(),
                    majorPath.last()
                ).size - oldNumOfPairs
            } else {
                val SDlinks = majorPath.first().links
                    .filter {
                        it.entangled &&
                            !it.swappedAt(majorPath.first()) &&
                            it.contains(majorPath.last()) &&
                            !it.utilized
                    }
                    .sortedBy { it.id }

                if (SDlinks.isNotEmpty()) {
                    succ = SDlinks.size.coerceAtMost(width)
                    (0 until succ).forEach { pid ->
                        SDlinks[pid].utilize()
                    }
                }
            }

            // fidelity instrumentation
            val estF =
                if (succ > 0 && lastSuccessfulPathForLog != null && lastSuccessfulPathForLog!!.size > 1) {
                    topo.pathEndToEndFidelity(lastSuccessfulPathForLog!!)
                } else 0.0

            val qualifiedSucc = if (succ > 0 && estF + 1e-12 >= FTH) succ else 0

            logWriter.appendln(
                """ ${majorPath.map { it.id }}, $width $succ $estF $qualifiedSucc"""
            )

            pathToRecoveryPaths[pathWithWidth].forEach {
                logWriter.appendln(
                    """  ${it.path.map { it.id }}, $width ${it.available} ${it.taken}"""
                )
            }
        }

        logWriter.appendln()
    }
}