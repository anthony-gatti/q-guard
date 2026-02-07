package quantum

import quantum.Fidelity
import quantum.topo.Topo
import quantum.topo.Node
import kotlin.math.roundToInt

data class PurifyResult(
    val success: Boolean,
    val Fbefore: Double,
    val Fafter: Double,
    val attempts: Int,
    val pairsConsumed: Int,
    val costUnits: Int,
    val psuccs: List<Double>
)

/**
 * Try to raise the best pair on hop (u,v) toward targetF by consuming extra pairs on that hop.
 * - deterministic=true: always treat BBPSSW attempt as success (upper bound / debugging).
 * - costPerAttempt: purification cost unit (C_pur)
 */
fun tryPurifyOnEdge(
    topo: Topo,
    u: Node, v: Node,
    targetF: Double,
    deterministic: Boolean = true,
    costPerAttempt: Int = 1
): PurifyResult {
    val pool = topo.linksBetween(u, v)
        .filter { it.entangled && it.notSwapped() && !it.utilized }
        .sortedBy { it.id }
        .toMutableList()

    if (pool.size < 2) return PurifyResult(false, 0.0, 0.0, 0, 0, 0, emptyList())

    var attempts = 0
    var pairsConsumed = 0
    var costUnits = 0
    val probs = mutableListOf<Double>()
    val Fbefore = pool.maxBy { it.fidelity }?.fidelity ?: 0.0

    val eps = 1e-12

    while (pool.size >= 2) {
        // Sort descending so pool[0] is the current best
        pool.sortByDescending { it.fidelity }

        // Consider only top K to keep this cheap
        val K = minOf(pool.size, 8)

        var bestI = -1
        var bestJ = -1
        var bestScore = Double.NEGATIVE_INFINITY
        var bestFp = 0.0
        var bestPs = 0.0

        // Search for the best safe pair among top K
        for (i in 0 until K) {
            for (j in i + 1 until K) {
                val fi = pool[i].fidelity
                val fj = pool[j].fidelity
                val (Fp, ps) = Fidelity.purifyWernerOnce(fi, fj)

                // safe = don't reduce the better input (fi >= fj since sorted)
                if (Fp + eps < fi) continue

                // Score:
                //   - If this could reach targetF on success, prefer higher ps strongly.
                //   - Otherwise, prefer higher expected improvement per expected pairs consumed.
                val expectedPairsConsumed = 2.0 - ps  // success consumes 1, failure consumes 2
                val score =
                    if (Fp + eps >= targetF) {
                        1e6 * ps / expectedPairsConsumed
                    } else {
                        (ps * (Fp - fi)) / expectedPairsConsumed
                    }

                if (score > bestScore) {
                    bestScore = score
                    bestI = i
                    bestJ = j
                    bestFp = Fp
                    bestPs = ps
                }
            }
        }

        // No safe purification move exists
        if (bestI < 0) break

        // Remove chosen links from pool
        val j = bestJ
        val i = bestI
        val b = pool.removeAt(j)
        val a = pool.removeAt(i)

        val Fp = bestFp
        val ps = bestPs

        probs += ps
        attempts += 1
        costUnits += costPerAttempt

        val pass = deterministic || (randGen.nextDouble() < ps)
        if (pass) {
            // Success: keep improved a, consume b
            a.fidelity = Fp
            b.utilize()
            pairsConsumed += 1

            if (Fp + eps >= targetF) {
                pool.add(a)
                return PurifyResult(true, Fbefore, Fp, attempts, pairsConsumed, costUnits, probs)
            } else {
                pool.add(a)
            }
        } else {
            // Failure: consume both
            a.utilize()
            b.utilize()
            pairsConsumed += 2
        }
    }

    val best = pool.maxBy { it.fidelity }?.fidelity ?: 0.0
    return PurifyResult(false, Fbefore, best, attempts, pairsConsumed, costUnits, probs)
}

/**
 * PurificationCostTable:
 *
 * Given an initial Werner fidelity F0 and a target per-hop fidelity Ftarget,
 * return the minimal number of *extra* pairs needed in the ideal BBPSSW model
 * (always-success purification, infinite pool of identical F0 pairs).
 *
 * - Each BBPSSW *round* takes 2 input pairs and returns 1 output pair.
 *   We treat that as "1 extra pair consumed" for cost purposes.
 * - If the Werner map converges below Ftarget (no further improvement),
 *   we return Int.MAX_VALUE to signal "infeasible".
 */
object PurificationCostTable {

    /**
     * Compute minimal number of extra pairs (cost) needed to reach Ftarget
     * starting from F0 using ideal BBPSSW on Werner states.
     *
     * @param F0        initial fidelity (Werner)
     * @param Ftarget   required per-hop target fidelity
     * @param maxRounds safety cap on the number of purification rounds to try
     */
    fun minCostToReach(
        F0: Double,
        Ftarget: Double,
        maxRounds: Int = 20
    ): Int {
        // If we already meet the target, no extra pairs needed.
        if (F0 + 1e-12 >= Ftarget) return 0

        var currentF = F0
        var cost = 0

        repeat(maxRounds) {
            // Idealized symmetric BBPSSW: both inputs have the same fidelity
            val (Fp, _) = Fidelity.purifyWernerOnce(currentF, currentF)

            // If we don't improve, we've hit the fixed point; can't reach target.
            if (Fp <= currentF + 1e-12) {
                return Int.MAX_VALUE
            }

            cost += 1
            currentF = Fp

            if (currentF + 1e-12 >= Ftarget) {
                return cost
            }
        }

        // If we hit maxRounds without reaching target, treat as infeasible.
        return Int.MAX_VALUE
    }
}