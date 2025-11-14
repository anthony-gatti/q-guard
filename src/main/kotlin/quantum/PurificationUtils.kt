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
    var Fbefore = pool.maxBy { it.fidelity }?.fidelity ?: 0.0

    while (pool.size >= 2) {
        pool.sortByDescending { it.fidelity }
        val a = pool.removeAt(0)
        val b = pool.removeAt(0)

        val (Fp, ps) = Fidelity.purifyWernerOnce(a.fidelity, b.fidelity)
        probs += ps
        attempts += 1
        costUnits += costPerAttempt

        val pass = deterministic || (randGen.nextDouble() < ps)
        if (pass) {
            // Success: keep improved 'a', consume 'b'
            a.fidelity = Fp
            b.utilize()
            pairsConsumed += 1
            if (Fp + 1e-12 >= targetF) {
                pool.add(a)
                return PurifyResult(true, Fbefore, Fp, attempts, pairsConsumed, costUnits, probs)
            } else {
                pool.add(a)
            }
        } else {
            // Failure: consume both
            a.utilize(); b.utilize()
            pairsConsumed += 2
            // keep going if more pairs remain
        }
    }

    val best = pool.maxBy { it.fidelity }?.fidelity ?: 0.0
    return PurifyResult(false, Fbefore, best, attempts, pairsConsumed, costUnits, probs)
}

/**
 * Deterministic purification cost table for EXG calculation ONLY.
 *
 * Assumes:
 *  - Werner inputs
 *  - BBPSSW protocol (Fidelity.purifyWernerOnce)
 *  - Always-success model: repeatedly apply F' from purifyWernerOnce(F,F)
 *    until F >= targetF or we stop making progress.
 *
 * Returned cost = number of *extra* pairs consumed (successful "sacrifice one, keep one" steps).
 */
object PurificationCostTable {
    // Fidelity values are clamped into [0.25, 0.999] and discretized to 1e-3
    private const val F_MIN = 0.25
    private const val F_MAX = 0.999
    private const val STEP = 0.001

    private fun indexForF(F: Double): Int {
        val clamped = F.coerceIn(F_MIN, F_MAX)
        return (clamped / STEP).roundToInt()
    }

    // Cache keyed by (F0_index, F_target_index) -> cost
    private val cache = mutableMapOf<Pair<Int, Int>, Int>()

    /**
     * Minimal deterministic cost (in extra pairs) to raise a Werner fidelity
     * from F0 to at least targetF, under "always succeed" BBPSSW.
     *
     * If F0 >= targetF already, cost = 0.
     * If we cannot make progress (F' <= F), returns Int.MAX_VALUE as "infeasible".
     */
    fun minCostToReach(F0: Double, targetF: Double): Int {
        if (F0 + 1e-12 >= targetF) return 0

        val i0 = indexForF(F0)
        val iT = indexForF(targetF)
        val key = i0 to iT

        cache[key]?.let { return it }

        var F = F0.coerceIn(F_MIN, F_MAX)
        var attempts = 0
        var safety = 1000  // guard against weird convergence

        while (F + 1e-12 < targetF && safety-- > 0) {
            val (Fp, _) = Fidelity.purifyWernerOnce(F, F)
            if (Fp <= F + 1e-12) {
                // No progress -> treat as infeasible
                attempts = Int.MAX_VALUE
                break
            }
            F = Fp
            attempts += 1
        }

        val cost = attempts
        cache[key] = cost
        return cost
    }
}