package quantum

object Fidelity {
    fun wFromF(F: Double): Double = (4.0 * F - 1.0) / 3.0
    fun fFromW(w: Double): Double = (1.0 + 3.0 * w) / 4.0

    fun swappedF(F1: Double, F2: Double): Double {
        val w1 = wFromF(F1)
        val w2 = wFromF(F2)
        return fFromW(w1 * w2)
    }

    // One depolarizing pass at creation:
    // F(0) = 1/4 + (3/4) * exp(-1 / tau)
    fun freshLinkFidelity(tau: Double): Double {
        val t = 7.0
        val base = 0.25
        return (base + (1.0 - base) * Math.exp(-1.0 / t)).coerceIn(0.25, 1.0)
    }

    // Keep for reference/tests only; you’re not using time decay > 0.
    fun memoryFidelity(t: Int, tau: Double, F0: Double = 1.0): Double {
        val base = 0.25
        return base + (F0 - base) * Math.exp(-(t + 1) / tau)
    }

    fun perHopTargetF(Fth: Double, hops: Int): Double {
        val wth = wFromF(Fth)
        val wHop = Math.pow(wth, 1.0 / hops)
        return fFromW(wHop)
    }

    // BBPSSW for Werner inputs: returns (F', p_succ)
    fun purifyWernerOnce(Fa: Double, Fb: Double): Pair<Double, Double> {
        // Symmetric case often uses Fa==Fb; we keep general form
        val a = Fa; val b = Fb
        val num = a*a + ((1 - a)*(1 - b))/9.0
        val den = a*a + (a*(1 - b) + (1 - a)*b)/3.0 + 5.0*((1 - a)*(1 - b))/9.0
        val Fp  = if (den > 0) (num / den).coerceIn(0.25, 1.0) else 0.25
        val ps  = den.coerceIn(0.0, 1.0)   // keep as a probability
        return Fp to ps
    }

    // Legacy (identical per-hop case) – not used by the gate anymore
    fun endToEndF(baseF: Double, hops: Int): Double {
        if (hops <= 0) return 0.0
        val w = wFromF(baseF)
        return fFromW(Math.pow(w, hops.toDouble()))
    }

    const val DEFAULT_TAU: Double = 7.0
    fun freshLinkFidelityDefault(): Double = freshLinkFidelity(DEFAULT_TAU)
}