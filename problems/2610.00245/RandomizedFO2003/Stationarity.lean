import RandomizedFO2003.Algebra

namespace RandomizedFO2003

/-- Scalar gate properties used by the activation argument. Smoothness is not needed here. -/
structure FlatGate where
  value : ℝ → ℝ
  flat : ∀ x, x ≤ 1 / 4 → value x = 0
  full : ∀ x, 1 / 2 ≤ x → value x = 1

theorem flat_of_abs_le (χ : FlatGate) {v : ℝ} (hv : |v| ≤ 1 / 4) :
    χ.value v = 0 := χ.flat v ((le_abs_self v).trans hv)

/-- The projected stationarity inequality propagates activation along the whole chain.
Derivation of this inequality from the actual gradient is a separate analytic obligation. -/
theorem all_gates_active
    (χ : FlatGate) (v c s : ℕ → ℝ) (N : ℕ)
    (hc₀ : c 0 = 1)
    (hc : ∀ i, c (i + 1) = χ.value (v i))
    (hs : ∀ i < N, 1 ≤ s i)
    (hproj : ∀ i < N, c i * s i - 1 / 8 ≤ v i) :
    ∀ i < N, χ.value (v i) = 1 := by
  intro i hi
  induction i with
  | zero =>
    have h := hproj 0 hi
    rw [hc₀, one_mul] at h
    apply χ.full
    linarith [hs 0 hi]
  | succ i ih =>
    have hprev := ih (by omega)
    have h := hproj (i + 1) hi
    rw [hc i, hprev, one_mul] at h
    apply χ.full
    linarith [hs (i + 1) hi]

/-- A small residual contradicts the early readout bound. -/
theorem residual_barrier
    (readout α α₀ ε γ : ℝ)
    (hα₀ : 0 < α₀)
    (hdual : α - ε / γ ≤ readout)
    (hscale : 3 * α₀ / 4 ≤ α - ε / γ)
    (hearly : |readout / α₀| ≤ 1 / 4) : False := by
  have hup : readout / α₀ ≤ 1 / 4 := (le_abs_self _).trans hearly
  have hup' := (div_le_iff₀ hα₀).mp hup
  linarith

end RandomizedFO2003
