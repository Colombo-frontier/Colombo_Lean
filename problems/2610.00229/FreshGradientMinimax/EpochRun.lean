import FreshGradientMinimax.EpochRecurrence

/-! Finite actual accelerated runs, with propagated potential integrability
and a noise floor separating the frozen reference energy from the initial
accelerated potential. -/

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace SCObjective
variable {dx dy : ℕ} {ℓ μ α σ : ℝ} (S : SCObjective dx dy ℓ μ α)

def epochForcing (ρ m H e σ : ℝ) (b : ℕ) (u : Euclid dx) (v : Euclid dy) : ℝ :=
  6 * ρ * Real.sqrt (m / H) * (m * ‖u - S.sliceMin v‖ ^ 2) +
    2 * ρ * Real.sqrt (m / H) * e + (140 * (estimatorCutoff ρ m e σ + 1 : ℝ) * σ ^ 2) / (H * b)

def epochAcceleratedKernel (O : FreshOracle S.toNCObjective σ) (ρ m H e : ℝ)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) (b : ℕ) (u : Euclid dx) (n : ℕ) :
    Kernel (Joint dy dy) (Joint dy dy) := iterateKernel (S.epochStepKernel O ρ m H e r hr b u) n

instance epochAcceleratedKernel_markov (O : FreshOracle S.toNCObjective σ) (ρ m H e : ℝ)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) (b : ℕ) (u : Euclid dx) (n : ℕ) :
    IsMarkovKernel (S.epochAcceleratedKernel O ρ m H e r hr b u n) := by
  unfold epochAcceleratedKernel
  infer_instance

theorem epochAcceleratedKernel_contract (O : FreshOracle S.toNCObjective σ)
    (hαℓ : α ≤ ℓ) (hfast : ℓ / 4 ≤ α) {ρ m H e : ℝ}
    (hρ : 0 < ρ) (hρsmall : ρ ≤ 1 / 1152) (hm : 0 < m) (hmH : m ≤ H) (he : 0 < e)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) {Q : Euclid dy → ℝ}
    (model : SmoothStrongModel Q (fun v => gradient S.effectiveValue v + r v) m H)
    (v : Euclid dy) (hmin : ∀ t, Q v ≤ Q t) {b : ℕ} (hb : 0 < b)
    (u : Euclid dx) (n : ℕ) (s : Joint dy dy) :
    Integrable (statePotential Q m v) (S.epochAcceleratedKernel O ρ m H e r hr b u n s) ∧
    (∫ t, statePotential Q m v t ∂S.epochAcceleratedKernel O ρ m H e r hr b u n s) ≤
      (1 - Real.sqrt (m / H) / 3) ^ n * statePotential Q m v s +
        S.epochForcing ρ m H e σ b u v * ∑ j ∈ Finset.range n, (1 - Real.sqrt (m / H) / 3) ^ j := by
  have hP : StronglyMeasurable (statePotential Q m v) :=
    (statePotential_continuous model.continuous m v).stronglyMeasurable
  have hpos (s : Joint dy dy) : 0 ≤ statePotential Q m v s :=
    SmoothStrongModel.potential_nonneg hm.le v hmin s.1 s.2
  have hi := S.epochStepKernel_potential_integrable O hαℓ hfast hρ hm he r hr model v hmin hb u
  have hstep (s : Joint dy dy) :
      (∫ t, statePotential Q m v t ∂S.epochStepKernel O ρ m H e r hr b u s) ≤
        (1 - Real.sqrt (m / H) / 3) * statePotential Q m v s + S.epochForcing ρ m H e σ b u v := by
    simpa only [epochForcing, add_assoc] using
      S.epochStepKernel_potential_bound O hαℓ hfast hρ hρsmall hm hmH he r hr model v hmin hb u s
  have hnonneg : 0 ≤ 1 - Real.sqrt (m / H) / 3 := by
    have ha1 := (acceleration_parameter hm hmH).2.1
    linarith
  exact ⟨iterateKernel_integrable _ _ hP hpos hi hstep n s,
    iterateKernel_moment _ _ hP hpos hi hnonneg hstep n s⟩

theorem epochAcceleratedKernel_error_floor (O : FreshOracle S.toNCObjective σ)
    (hαℓ : α ≤ ℓ) (hfast : ℓ / 4 ≤ α) {ρ m H e : ℝ}
    (hρ : 0 < ρ) (hρsmall : ρ ≤ 1 / 1152) (hm : 0 < m) (hmH : m ≤ H) (he : 0 < e)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) {Q : Euclid dy → ℝ}
    (model : SmoothStrongModel Q (fun v => gradient S.effectiveValue v + r v) m H)
    (v : Euclid dy) (hmin : ∀ t, Q v ≤ Q t) {b : ℕ} (hb : 0 < b)
    (u : Euclid dx) (n : ℕ) (s : Joint dy dy) :
    (∫ t, statePotential Q m v t ∂S.epochAcceleratedKernel O ρ m H e r hr b u n s) ≤
      (1 - Real.sqrt (m / H) / 3) ^ n * statePotential Q m v s +
      18 * ρ * (m * ‖u - S.sliceMin v‖ ^ 2) + 6 * ρ * e +
      3 * (140 * (estimatorCutoff ρ m e σ + 1 : ℝ) * σ ^ 2) / (Real.sqrt (m / H) * H * b) := by
  let a := Real.sqrt (m / H)
  have hH : 0 < H := hm.trans_le hmH
  have ha : 0 < a := Real.sqrt_pos.mpr (div_pos hm hH)
  have ha1 : a ≤ 1 := (acceleration_parameter hm hmH).2.1
  have hcoeff : 0 ≤ 1 - a / 3 := by linarith
  have hcoeff1 : 1 - a / 3 < 1 := by linarith
  have hsum : (∑ j ∈ Finset.range n, (1 - a / 3) ^ j) ≤ 1 / (a / 3) := by
    simpa only [Nat.Ico_zero_eq_range, pow_zero, sub_sub_cancel] using
      (geom_sum_Ico_le_of_lt_one hcoeff hcoeff1 (m := 0) (n := n))
  have hF : 0 ≤ S.epochForcing ρ m H e σ b u v := by unfold epochForcing; positivity
  have hmul := mul_le_mul_of_nonneg_left hsum hF
  have hbound := (S.epochAcceleratedKernel_contract O hαℓ hfast hρ hρsmall hm hmH he
    r hr model v hmin hb u n s).2
  have heq : S.epochForcing ρ m H e σ b u v * (1 / (a / 3)) =
      18 * ρ * (m * ‖u - S.sliceMin v‖ ^ 2) + 6 * ρ * e +
      3 * (140 * (estimatorCutoff ρ m e σ + 1 : ℝ) * σ ^ 2) / (a * H * b) := by
    change (6 * ρ * a * (m * ‖u - S.sliceMin v‖ ^ 2) + 2 * ρ * a * e +
      (140 * (estimatorCutoff ρ m e σ + 1 : ℝ) * σ ^ 2) / (H * b)) * (1 / (a / 3)) = _
    field_simp
    ring
  rw [heq] at hmul
  linarith only [hbound, hmul]

end SCObjective
end FreshGradientMinimax
