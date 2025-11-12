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
}