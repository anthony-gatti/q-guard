package quantum.algorithm

import quantum.topo.*
import quantum.Fidelity
import utils.ReducibleLazyEvaluation

class FidelityGuaranteedOnlineAlgorithm(
    topo: Topo,
    allowRecoveryPaths: Boolean = true
) : OnlineAlgorithm(topo, allowRecoveryPaths) {

    // label for logs / plot legends
    override val name: String = "TEMP-NAME-QCAST"


    private val F_TH = 0.8 // hardcoded for now
    private val TAU = Fidelity.DEFAULT_TAU
    private val F_BASE: Double = Fidelity.freshLinkFidelity(TAU)

    // Same Q-CAST P4 logic, but with fidelity logging / qualification
    override fun P4() {
        majorPaths.forEach { pathWithWidth ->
            val (_, width, majorPath) = pathWithWidth

            val hops = majorPath.size - 1
            val predF = Fidelity.endToEndF(F_BASE, hops)

            if (predF < F_TH) {
                logWriter.appendln(
                    """ ${majorPath.map { it.id }}, $width 0 $predF 0"""
                )
                logWriter.appendln()
                return@forEach
            }

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

            // Our fidelity instrumentation
            val estF =
                if (succ > 0 && majorPath.size > 1) topo.pathEndToEndFidelity(majorPath)
                else 0.0

            val qualifiedSucc = if (succ > 0 && estF >= F_TH) succ else 0

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