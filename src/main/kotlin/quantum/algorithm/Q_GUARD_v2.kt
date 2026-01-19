package quantum.algorithm

import quantum.Fidelity
import quantum.PurificationCostTable
import quantum.topo.*
import utils.ReducibleLazyEvaluation
import utils.also
import utils.pmap
import utils.require
import java.util.LinkedList
import java.util.PriorityQueue
import kotlin.collections.HashMap
import kotlin.math.pow

/**
 * Q_GUARD_v2 (renamed by you) is now the "PredEXG / Phase-2 fidelity-aware" variant:
 * - Phase 2 uses EXT(path,w) * predictedPurificationYield(path,w,Fth) for major path selection.
 * - Recovery paths are generated with a *segment budget* derived from the major path's threshold.
 * - Phase 4 execution stays exactly as Q_GUARD (we inherit it unchanged).
 *
 * This replaces the old "weighted targets" v2; targets are equal-split by hop count.
 */
class Q_GUARD_v2(
    topo: Topo,
    allowRecoveryPaths: Boolean = true
) : Q_GUARD(topo, allowRecoveryPaths) {

    override val name: String = "QG-v2"   // change label if you want

    /**
     * Phase-2 scoring hook used inside calCandidates():
     * Option A: EXT already accounts for link success, so yield only reflects purification overhead.
     */
    override fun scoreCandidate(path: Path, width: Int, oldP: DoubleArray): Double {
        val base = topo.e(path, width, oldP)
        if (base <= 0.0) return 0.0

        // Major candidates: endpoints correspond to the actual request (src,dst).
        val fth = fthFor(path.first(), path.last())
        val y = predictedYieldEqualSplit(path, width, fth)
        return if (y > 0.0) base * y else 0.0
    }

    /**
     * IMPORTANT:
     * OnlineAlgorithm.P2() calls OnlineAlgorithm.P2Extra() (which is NOT open),
     * and P2Extra would score recovery paths using fthFor(switch_i, switch_j) incorrectly.
     *
     * So we override P2() and call our own recovery generator that uses segment budgets.
     */
    override fun P2() {
        require({ topo.isClean() })
        majorPaths.clear()
        recoveryPaths.clear()
        pathToRecoveryPaths.clear()

        while (true) {
            val candidates = calCandidates(srcDstPairs)   // uses overridden scoreCandidate()
            val pick = candidates.maxBy { it.first }
            if (pick != null && pick.first > 0.0) {
                pickAndAssignPath(pick)
            } else {
                break
            }
        }

        if (allowRecoveryPaths) {
            P2ExtraPredBudget()
        }
    }

    /**
     * Recovery-path generation, structurally identical to OnlineAlgorithm.P2Extra(),
     * except scoring uses a segment fidelity budget derived from the major path's threshold.
     */
    private fun P2ExtraPredBudget() {
        majorPaths.forEach { majorPicked ->
            val (_, _, majorPath) = majorPicked
            val majorSrc = majorPath.first()
            val majorDst = majorPath.last()
            val majorFth = fthFor(majorSrc, majorDst)

            val Hmajor = majorPath.size - 1
            if (Hmajor <= 0) return@forEach

            val wTh = Fidelity.wFromF(majorFth)

            (1..topo.k).forEach { l ->
                (0..majorPath.size - l - 1).forEach { i ->
                    val segSrc = majorPath[i]
                    val segDst = majorPath[i + l]

                    // Segment Werner budget: w_seg = w_th^(l / Hmajor)
                    val wSeg = wTh.pow(l.toDouble() / Hmajor.toDouble())

                    val pick = calCandidateWithWernerBudget(segSrc, segDst, wSeg)
                    if (pick != null && pick.first > 0.0) {
                        pickAndAssignPath(pick, majorPicked)
                    }
                }
            }
        }
    }

    /**
     * Like OnlineAlgorithm.calCandidates() but for ONE (src,dst) pair with a fixed Werner budget.
     * Scoring: EXT(path,w) * predictedYieldForWernerBudget(path,w,wBudget)
     */
    private fun calCandidateWithWernerBudget(src: Node, dst: Node, wBudget: Double): PickedPath? {
        val maxM = minOf(src.remainingQubits, dst.remainingQubits)
        if (maxM == 0) return null

        var candidate: PickedPath? = null

        for (w in (maxM downTo 1)) {
            val failNodes = (topo.nodes - src - dst).filter { it.remainingQubits < 2 * w }.toHashSet()

            val edges: HashSet<Edge> = topo.links
                .filter { !it.assigned && it.n1 !in failNodes && it.n2 !in failNodes }
                .groupBy { it.n1 to it.n2 }
                .filter { it.value.size >= w }
                .map { it.key }
                .toHashSet()

            val neighborsOf = ReducibleLazyEvaluation<Node, MutableList<Node>>({ mutableListOf() })
            edges.forEach {
                neighborsOf[it.n1].add(it.n2)
                neighborsOf[it.n2].add(it.n1)
            }

            if (neighborsOf[src].isEmpty() || neighborsOf[dst].isEmpty()) continue

            val prevFromSrc: HashMap<Node, Node> = hashMapOf()

            fun getPathFromSrc(n: Node): MutableList<Node> {
                val path = LinkedList<Node>()
                var cur = n
                while (cur != topo.sentinal) {
                    path.addFirst(cur)
                    cur = prevFromSrc[cur]!!
                }
                return path.toMutableList()
            }

            val E = topo.nodes.map { Double.NEGATIVE_INFINITY to DoubleArray(w + 1) { 0.0 } }.toTypedArray()
            val q = PriorityQueue<quantum.topo.Edge>(Comparator { (o1, _), (o2, _) ->
                -E[o1.id].first.compareTo(E[o2.id].first)
            })

            E[src.id] = Double.POSITIVE_INFINITY to DoubleArray(w + 1) { 0.0 }
            q.offer(src to topo.sentinal)

            while (q.isNotEmpty()) {
                val (u, prev) = q.poll()
                if (u in prevFromSrc) continue
                prevFromSrc[u] = prev

                if (u == dst) {
                    candidate = E[u.id].first to w also getPathFromSrc(dst)
                    break
                }

                neighborsOf[u].forEach { neighbor ->
                    val tmp = E[u.id].second.clone()

                    val path = getPathFromSrc(u) + neighbor
                    val base = topo.e(path, w, tmp)
                    val y = predictedYieldForWernerBudget(path, w, wBudget)
                    val e = if (base > 0.0 && y > 0.0) base * y else 0.0

                    val newE = e to tmp
                    val oldE = E[neighbor.id]

                    if (oldE.first < newE.first) {
                        E[neighbor.id] = newE
                        q.offer(neighbor to u)
                    }
                }
            }

            if (candidate != null) break
        }

        return candidate
    }

    /**
     * Predicted yield using equal-split per-hop target derived from end-to-end Fth.
     * Yield is the bottleneck hop's 1 / 2^(roundsNeeded).
     *
     * Feasible only if 2^(roundsNeeded) <= width on every hop.
     */
    private fun predictedYieldEqualSplit(path: Path, width: Int, fthEndToEnd: Double): Double {
        val hops = path.size - 1
        if (hops <= 0) return 0.0

        val perHopTarget = Fidelity.perHopTargetF(fthEndToEnd, hops)
        val hopInfo = topo.perHopFreshF(path)   // (edge, tau, F0)

        var bottleneck = 1.0

        for ((edge, _, F0) in hopInfo) {
            val rounds = PurificationCostTable.minCostToReach(F0, perHopTarget)
            if (rounds == Int.MAX_VALUE) return 0.0

            // Need at least 2^rounds raw pairs on this hop; width is the per-hop cap in a slot.
            if (rounds >= 31) return 0.0
            val required = 1 shl rounds
            if (required > width) return 0.0

            val hopYield = 1.0 / required.toDouble()
            if (hopYield < bottleneck) bottleneck = hopYield
        }

        return bottleneck
    }

    /**
     * Predicted yield for a recovery span when we want to preserve a fixed Werner budget wBudget
     * (derived from the major segment's share of the end-to-end threshold).
     *
     * For a candidate span with h hops: w_target_per_hop = wBudget^(1/h).
     */
    private fun predictedYieldForWernerBudget(path: Path, width: Int, wBudget: Double): Double {
        val hops = path.size - 1
        if (hops <= 0) return 0.0
        if (wBudget <= 0.0) return 0.0

        val wPerHop = wBudget.pow(1.0 / hops.toDouble())
        val perHopTarget = Fidelity.fFromW(wPerHop)

        val hopInfo = topo.perHopFreshF(path)

        var bottleneck = 1.0

        for ((_, _, F0) in hopInfo) {
            val rounds = PurificationCostTable.minCostToReach(F0, perHopTarget)
            if (rounds == Int.MAX_VALUE) return 0.0
            if (rounds >= 31) return 0.0
            val required = 1 shl rounds
            if (required > width) return 0.0
            val hopYield = 1.0 / required.toDouble()
            if (hopYield < bottleneck) bottleneck = hopYield
        }

        return bottleneck
    }
}