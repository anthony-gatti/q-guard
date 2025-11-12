package quantum

object Fidelity {
    fun wFromF(F: Double): Double = (4.0 * F - 1.0) / 3.0
    fun fFromW(w: Double): Double = (1.0 + 3.0 * w) / 4.0

    // Fidelity after swapping two Werner states with fidelities F1, F2
    fun swappedF(F1: Double, F2: Double): Double {
        val w1 = wFromF(F1)
        val w2 = wFromF(F2)
        val wOut = w1 * w2
        return fFromW(wOut)
    }

    // F(t) = 1/4 + (F0 - 1/4) * exp(-(t+1)/tau)
    fun memoryFidelity(t: Int, tau: Double, F0: Double = 1.0): Double {
        val base = 0.25
        return base + (F0 - base) * Math.exp(-(t + 1) / tau)
    }

    // For a freshly generated link (t = 0)
    fun freshLinkFidelity(tau: Double): Double =
        memoryFidelity(0, tau)

    // Convenience: default tau chosen so F(0) ≈ 0.9
    // Solve: 0.9 = 1/4 + (3/4) e^{-1/tau}  ⇒  tau ≈ 6.99
    const val DEFAULT_TAU: Double = 7.0

    fun freshLinkFidelityDefault(): Double =
        freshLinkFidelity(DEFAULT_TAU)

    // Deterministic end-to-end fidelity with identical per-hop base F and L hops
    fun endToEndF(baseF: Double, hops: Int): Double {
        if (hops <= 0) return 0.0
        val w = wFromF(baseF)
        val wL = Math.pow(w, hops.toDouble())
        return fFromW(wL)
    }
}