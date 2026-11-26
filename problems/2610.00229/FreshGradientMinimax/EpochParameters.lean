import FreshGradientMinimax.EpochRun

/-! Explicit accelerated-phase parameters from F.3, including a linear
bound in the actual initial energy. The batch uses the epoch envelope,
while the multilevel cutoff continues to use the final target `e`. -/

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory

def epochRho : ℝ := 1 / (10000000000 * 17 ^ 2)

theorem epochRho_pos : 0 < epochRho := by norm_num [epochRho]

theorem epochRho_small : epochRho ≤ 1 / 1152 := by norm_num [epochRho]

def epochSteps (m H : ℝ) : ℕ := ⌈(3 / Real.sqrt (m / H)) * Real.log (10000000 * 17)⌉₊

def epochBatch (m H e σ E : ℝ) : ℕ :=
  max 1 ⌈(100000000 * 17 * (140 * (estimatorCutoff epochRho m e σ + 1 : ℝ) * σ ^ 2)) /
    (E * Real.sqrt (m * H))⌉₊

theorem epochBatch_pos (m H e σ E : ℝ) : 0 < epochBatch m H e σ E :=
  lt_of_lt_of_le (by decide : 0 < (1 : ℕ)) (le_max_left _ _)

theorem epochSteps_contraction {m H : ℝ} (hm : 0 < m) (hmH : m ≤ H) :
    (1 - Real.sqrt (m / H) / 3) ^ epochSteps m H ≤ 1 / (10000000 * 17 : ℝ) := by
  have hH := hm.trans_le hmH
  have ha : 0 < Real.sqrt (m / H) := Real.sqrt_pos.mpr (div_pos hm hH)
  have ha1 := (acceleration_parameter hm hmH).2.1
  have h := geometric_decay_log_ceiling (by positivity : 0 < Real.sqrt (m / H) / 3)
    (by linarith : Real.sqrt (m / H) / 3 ≤ 1) (by norm_num : (0 : ℝ) < 10000000 * 17)
  have heq : Real.log (10000000 * 17) / (Real.sqrt (m / H) / 3) =
      (3 / Real.sqrt (m / H)) * Real.log (10000000 * 17) := by ring
  rw [heq] at h
  exact h

theorem epochBatch_noise {m H e σ E : ℝ} (hm : 0 < m) (hmH : m ≤ H) (hE : 0 < E) :
    3 * (140 * (estimatorCutoff epochRho m e σ + 1 : ℝ) * σ ^ 2) /
      (Real.sqrt (m / H) * H * epochBatch m H e σ E) ≤ 3 * E / (100000000 * 17 : ℝ) := by
  have hH : 0 < H := hm.trans_le hmH
  have ha : 0 < Real.sqrt (m / H) := Real.sqrt_pos.mpr (div_pos hm hH)
  have hroot : 0 < Real.sqrt (m * H) := Real.sqrt_pos.mpr (mul_pos hm hH)
  have hb : (0 : ℝ) < epochBatch m H e σ E := by exact_mod_cast epochBatch_pos m H e σ E
  have hprod : Real.sqrt (m / H) * H = Real.sqrt (m * H) := by
    apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt (div_nonneg hm.le hH.le), Real.sq_sqrt (mul_nonneg hm.le hH.le)]
    field_simp
    ring
  have hceil : (100000000 * 17 * (140 * (estimatorCutoff epochRho m e σ + 1 : ℝ) * σ ^ 2)) /
      (E * Real.sqrt (m * H)) ≤ (epochBatch m H e σ E : ℝ) := by
    exact (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right _ _))
  have hsize := (div_le_iff₀ (mul_pos hE hroot)).mp hceil
  rw [hprod]
  apply (div_le_div_iff₀ (mul_pos hroot hb) (by norm_num)).mpr
  nlinarith only [hsize]

namespace SCObjective
variable {dx dy : ℕ} {ℓ μ α σ : ℝ} (S : SCObjective dx dy ℓ μ α)

/-- A pointwise bound linear in the initial energy, for later averaging over
random inputs. No bound on that energy is assumed in this theorem. -/
theorem epochAcceleratedKernel_selected_bound (O : FreshOracle S.toNCObjective σ)
    (hαℓ : α ≤ ℓ) (hfast : ℓ / 4 ≤ α) {m H e E : ℝ}
    (hm : 0 < m) (hmH : m ≤ H) (he : 0 < e) (heE : e ≤ E)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) {Q : Euclid dy → ℝ}
    (model : SmoothStrongModel Q (fun v => gradient S.effectiveValue v + r v) m H)
    (v : Euclid dy) (hmin : ∀ t, Q v ≤ Q t) (u : Euclid dx) (x : Euclid dy) :
    (∫ t, statePotential Q m v t
      ∂S.epochAcceleratedKernel O epochRho m H e r hr (epochBatch m H e σ E) u (epochSteps m H) (x, x)) ≤
      (Q x - Q v + m * ‖u - S.sliceMin v‖ ^ 2) / (1000000 * 17) + E / (1000000 * 17) := by
  have hE : 0 < E := he.trans_le heE
  have hfloor := S.epochAcceleratedKernel_error_floor O hαℓ hfast epochRho_pos epochRho_small hm hmH he
    r hr model v hmin (epochBatch_pos m H e σ E) u (epochSteps m H) (x, x)
  have hP : 0 ≤ statePotential Q m v (x, x) := SmoothStrongModel.potential_nonneg hm.le v hmin x x
  have hdecay := mul_le_mul_of_nonneg_right (epochSteps_contraction hm hmH) hP
  have hinit := model.potential_initial_bound v hmin x
  have hinit' := mul_le_mul_of_nonneg_left hinit (by norm_num : (0 : ℝ) ≤ 1 / (10000000 * 17))
  have hnoise := epochBatch_noise (e := e) (σ := σ) hm hmH hE
  have hg : 0 ≤ Q x - Q v := sub_nonneg.mpr (hmin x)
  have hu : 0 ≤ m * ‖u - S.sliceMin v‖ ^ 2 := by positivity
  have htarget := mul_le_mul_of_nonneg_left heE (by norm_num [epochRho] : 0 ≤ 6 * epochRho)
  change statePotential Q m v (x, x) ≤ 2 * (Q x - Q v) at hinit
  change (1 / (10000000 * 17 : ℝ)) * statePotential Q m v (x, x) ≤ _ at hinit'
  norm_num only [epochRho] at hfloor htarget hnoise ⊢
  nlinarith only [hfloor, hdecay, hinit', hnoise, hg, hu, htarget, hE.le]

/-- Formula (50) for a deterministic input satisfying its energy envelope. -/
theorem epochAcceleratedKernel_accuracy (O : FreshOracle S.toNCObjective σ)
    (hαℓ : α ≤ ℓ) (hfast : ℓ / 4 ≤ α) {m H e E : ℝ}
    (hm : 0 < m) (hmH : m ≤ H) (he : 0 < e) (heE : e ≤ E)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) {Q : Euclid dy → ℝ}
    (model : SmoothStrongModel Q (fun v => gradient S.effectiveValue v + r v) m H)
    (v : Euclid dy) (hmin : ∀ t, Q v ≤ Q t) (u : Euclid dx) (x : Euclid dy)
    (hinit : Q x - Q v + m * ‖u - S.sliceMin v‖ ^ 2 ≤ E) :
    (∫ t, statePotential Q m v t
      ∂S.epochAcceleratedKernel O epochRho m H e r hr (epochBatch m H e σ E) u (epochSteps m H) (x, x)) ≤
      E / (100000 * 17) := by
  have h := S.epochAcceleratedKernel_selected_bound O hαℓ hfast hm hmH he heE r hr model v hmin u x
  have hE := he.trans_le heE
  linarith

end SCObjective
end FreshGradientMinimax
