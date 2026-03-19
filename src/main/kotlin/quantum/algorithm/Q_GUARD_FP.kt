package quantum.algorithm

import quantum.Fidelity
import quantum.topo.*
import kotlin.math.pow
import kotlin.math.ln
import kotlin.math.exp

open class Q_GUARD_FP(
    topo: Topo,
    allowRecoveryPaths: Boolean = true
) : Q_GUARD(topo, allowRecoveryPaths) {

    override val name: String = "QG-FP"

    override fun scoreCandidate(path: Path, width: Int, oldP: DoubleArray): Double {
        return computeEXG(path, width)
    }

    private fun computeEXG(path: Path, width: Int): Double {
        val hops = path.size - 1
        if (hops <= 0) return 0.0
        if (width <= 0) return 0.0

        val fth = fthFor(path.first(), path.last())

        // Determine purification round counts per hop
        val rounds = effortRoundsForPath(path, width, fth)
            ?: return 0.0  // infeasible

        // c_k = 2^r_k = raw pairs consumed per purified output on hop k
        val costs = IntArray(hops) { k ->
            val r = rounds[k]
            if (r >= 31) return 0.0
            1 shl r
        }

        // M = max possible purified bottleneck width
        val M = costs.map { width / it }.min()!!
        if (M <= 0) return 0.0

        // Per-hop link success probabilities
        val hopPairs = path.dropLast(1).zip(path.drop(1))
        val linkPs = hopPairs.map { (u, v) ->
            val link = topo.linksBetween(u, v).first()
            Math.E.pow(-topo.alpha * link.l)
        }

        // Compute Q^k_i = Pr[hop k produces exactly i purified pairs]
        val Qprime = Array(hops) { k ->
            val ck = costs[k]
            val pk = linkPs[k]
            val dist = DoubleArray(M + 1)

            for (j in 0..width) {
                val bProb = binomialProb(width, j, pk)
                val purified = j / ck  // floor division
                if (purified >= M) {
                    dist[M] += bProb  // cap at M
                } else {
                    dist[purified] += bProb
                }
            }

            dist
        }

        // Bottleneck recurrence over purified outputs
        // P_i = Pr[min purified width across hops 1..k is exactly i]
        var P = Qprime[0].clone()

        for (k in 1 until hops) {
            val newP = DoubleArray(M + 1)

            // sumQ[i] = Pr[hop k produces >= i purified pairs]
            val sumQ = DoubleArray(M + 2)
            for (i in M downTo 0) {
                sumQ[i] = sumQ[i + 1] + Qprime[k][i]
            }

            // sumP[i] = = Pr[bottleneck so far >= i]
            val sumP = DoubleArray(M + 2)
            for (i in M downTo 0) {
                sumP[i] = sumP[i + 1] + P[i]
            }

            for (i in 0..M) {
                newP[i] = P[i] * sumQ[i] + Qprime[k][i] * sumP[i + 1]
            }

            P = newP
        }

        // EXG = q^(h-1) * sum(i * P[i])
        val numSwaps = (hops - 1).coerceAtLeast(0)
        val qPath = topo.q.pow(numSwaps.toDouble())

        var exg = 0.0
        for (i in 1..M) {
            exg += i * P[i]
        }
        exg *= qPath

        return exg
    }

    // equal-split round counts

    private fun effortRoundsForPath(path: Path, width: Int, fthEndToEnd: Double): IntArray? {
        val hops = path.size - 1
        if (hops <= 0) return null
        if (width <= 0) return null

        val fth = fthEndToEnd.coerceAtLeast(0.25)
        val perHopTarget = Fidelity.perHopTargetF(fth, hops)

        val hopPairs = path.dropLast(1).zip(path.drop(1))
        val rounds = IntArray(hops)

        for (i in 0 until hops) {
            val (u, v) = hopPairs[i]
            val link = topo.linksBetween(u, v).first()
            val F0 = Fidelity.freshLinkFidelity(link.tau)

            val r = quantum.PurificationCostTable.minCostToReach(F0, perHopTarget)
            if (r == Int.MAX_VALUE) return null  // infeasible

            if (r >= 31) return null
            if ((1 shl r) > width) return null

            rounds[i] = r
        }

        return rounds
    }

    private fun binomialProb(n: Int, k: Int, p: Double): Double {
        if (k < 0 || k > n) return 0.0
        if (p <= 0.0) return if (k == 0) 1.0 else 0.0
        if (p >= 1.0) return if (k == n) 1.0 else 0.0

        var logProb = 0.0
        for (i in 1..k) {
            logProb += ln((n - i + 1).toDouble()) - ln(i.toDouble())
        }
        logProb += k * ln(p) + (n - k) * ln(1.0 - p)

        return exp(logProb)
    }
}