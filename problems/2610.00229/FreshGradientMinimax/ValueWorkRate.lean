import FreshGradientMinimax.ScaledValueCost

/-! The F.3 rate for the actual accumulated work tags, with an explicit
universal constant. The algorithm-transcript implementation and uniform
random-objective parameterization remain separate obligations. -/

set_option autoImplicit false
set_option maxHeartbeats 2600000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory

theorem initialization_log_bound {E₀ e : ℝ} (hE₀ : 0 ≤ E₀) (he : 0 < e) :
    Real.log (max E₀ e / e) / Real.log 2 + 2 ≤ 6 * Real.log (2 + E₀ / e) := by
  have ht : 0 ≤ E₀ / e := div_nonneg hE₀ he.le
  have hlog : (1 / 2 : ℝ) ≤ Real.log (2 + E₀ / e) :=
    log_two_bounds.1.trans (Real.log_le_log (by norm_num) (by linarith))
  have hx : max E₀ e / e ≤ 2 + E₀ / e := by
    calc
      _ ≤ (2 * e + E₀) / e := div_le_div_of_nonneg_right (max_le (by linarith) (by linarith)) he.le
      _ = _ := by field_simp
  have hm := Real.log_le_log (div_pos (he.trans_le (le_max_right _ _)) he) hx
  have hdiv : Real.log (max E₀ e / e) / Real.log 2 ≤ 2 * Real.log (2 + E₀ / e) := by
    apply (div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
    have hp := mul_le_mul_of_nonneg_right log_two_bounds.1 (by linarith : 0 ≤ 2 * Real.log (2 + E₀ / e))
    nlinarith only [hm, hp]
  linarith only [hdiv, hlog]

theorem valueSolverWork_rate {ℓ α σ m H e E₀ : ℝ}
    (hℓ : 0 < ℓ) (hα : 0 < α) (hfast : ℓ / 4 ≤ α) (hm : 0 < m)
    (hmH : m ≤ H) (hHℓ : H ≤ 20 * ℓ) (he : 0 < e) (hE₀ : 0 ≤ E₀) :
    valueSolverWork ℓ α σ m H e E₀ ≤ 10 ^ 70 * valueLogFactor ℓ σ m e ^ 3 *
      (Real.sqrt (H / m) * Real.log (2 + E₀ / e) + σ ^ 2 / (m * e)) := by
  let L := valueLogFactor ℓ σ m e
  let T := Real.sqrt (H / m) * Real.log (2 + E₀ / e)
  let U := σ ^ 2 / (m * e)
  have hL := (valueLogFactor_bounds (σ := σ) hℓ hm he).1
  have hL0 : 0 ≤ L := by dsimp [L]; linarith
  have hT0 : 0 ≤ T := by
    apply mul_nonneg (Real.sqrt_nonneg _)
    apply Real.log_nonneg
    have ht := div_nonneg hE₀ he.le
    linarith
  have hU0 : 0 ≤ U := by dsimp [U]; positivity
  have hL23 : L ^ 2 ≤ L ^ 3 := by
    have h := mul_le_mul_of_nonneg_right hL (sq_nonneg L)
    nlinarith only [h]
  have hb := valueSolverWork_bound (σ := σ) (E₀ := E₀) hℓ hα hm (hm.trans_le hmH) he
  have hB := epochBaseWork_valueLog_bound (σ := σ) hℓ hα hfast hm hmH he
  have hN := epochNoiseWork_valueLog_bound (σ := σ) hℓ hα hfast hm hmH (hmH.trans hHℓ) he
  have hc := initialization_log_bound hE₀ he
  have hc0 : 0 ≤ Real.log (max E₀ e / e) / Real.log 2 + 2 := by
    have hR : 1 ≤ max E₀ e / e := (le_div_iff₀ he).mpr (by rw [one_mul]; exact le_max_right _ _)
    exact add_nonneg (div_nonneg (Real.log_nonneg hR) (by linarith [log_two_bounds.1])) (by norm_num)
  have hd := mul_le_mul hB hc hc0 (by positivity : 0 ≤ 10 ^ 42 * L ^ 2 * Real.sqrt (H / m))
  have hd' : epochBaseWork ℓ α σ m H e * (Real.log (max E₀ e / e) / Real.log 2 + 2) ≤
      (6 * 10 ^ 42) * L ^ 2 * T := by
    convert hd using 1
    dsimp [T, L]
    ring
  have hdp := mul_le_mul_of_nonneg_right hL23 (show 0 ≤ (6 * 10 ^ 42) * T by positivity)
  have hdet : epochBaseWork ℓ α σ m H e * (Real.log (max E₀ e / e) / Real.log 2 + 2) ≤
      (6 * 10 ^ 42) * L ^ 3 * T := by nlinarith only [hd', hdp]
  have hn := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hN (by norm_num : (0 : ℝ) ≤ 4)) he.le
  have hn' : 4 * epochNoiseWork ℓ α σ m H e / e ≤ (4 * 10 ^ 68) * L ^ 3 * U := by
    convert hn using 1
    dsimp [U, L]
    ring
  have hdet0 : 0 ≤ L ^ 3 * T := by positivity
  have hstat0 : 0 ≤ L ^ 3 * U := by positivity
  change _ ≤ 10 ^ 70 * L ^ 3 * (T + U)
  nlinarith only [hb, hdet, hn', hdet0, hstat0]

namespace SCObjective
variable {dx dy : ℕ} {ℓ μ α σ : ℝ} (S : SCObjective dx dy ℓ μ α)

theorem costedValueSolverKernel_random_rate (O : FreshOracle S.toNCObjective σ)
    (hfast : ℓ / 4 ≤ α) {m H e E₀ : ℝ} (hm : 0 < m) (hmH : m ≤ H) (hHℓ : H ≤ 20 * ℓ)
    (he : 0 < e) (hE₀ : 0 ≤ E₀) (r : Euclid dy → Euclid dy) (hr : Measurable r)
    (ν : Measure (Joint dx dy)) [IsProbabilityMeasure ν] :
    (∫ t, costValue t ∂S.costedValueSolverKernel O m H e E₀ r hr ∘ₘ ν) ≤
      10 ^ 70 * valueLogFactor ℓ σ m e ^ 3 *
        (Real.sqrt (H / m) * Real.log (2 + E₀ / e) + σ ^ 2 / (m * e)) := by
  rw [(S.costedValueSolverKernel_random_cost O m H e E₀ r hr ν).2]
  exact valueSolverWork_rate S.toNCObjective.L_pos S.α_pos hfast hm hmH hHℓ he hE₀

theorem costedValueSolverKernel_accuracy (O : FreshOracle S.toNCObjective σ)
    (hαℓ : α ≤ ℓ) (hfast : ℓ / 4 ≤ α) {m H e E₀ : ℝ}
    (hm : 0 < m) (hmH : m ≤ H) (he : 0 < e)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) {Q : Euclid dy → ℝ}
    (model : SmoothStrongModel Q (fun v => gradient S.effectiveValue v + r v) m H)
    (v : Euclid dy) (hmin : ∀ x, Q v ≤ Q x) (ν : Measure (Joint dx dy)) [IsProbabilityMeasure ν]
    (hInit : Integrable (S.solverEnergy Q m v) ν)
    (hEnergy : (∫ z, S.solverEnergy Q m v z ∂ν) ≤ E₀) :
    Integrable (fun t : Joint dx dy × ℕ => Q t.1.2 - Q v) (S.costedValueSolverKernel O m H e E₀ r hr ∘ₘ ν) ∧
    Integrable (fun t => S.fastError m t.1) (S.costedValueSolverKernel O m H e E₀ r hr ∘ₘ ν) ∧
    (∫ t, Q t.1.2 - Q v ∂S.costedValueSolverKernel O m H e E₀ r hr ∘ₘ ν) ≤ e ∧
    (∫ t, S.fastError m t.1 ∂S.costedValueSolverKernel O m H e E₀ r hr ∘ₘ ν) ≤ e := by
  obtain ⟨hg, hf, hgb, hfb⟩ := S.valueSolverKernel_accuracy O hαℓ hfast hm hmH he r hr model v hmin ν hInit hEnergy
  rw [← S.costedValueSolverKernel_output_law O m H e E₀ r hr ν] at hg hf hgb hfb
  have hgm : StronglyMeasurable (fun z : Joint dx dy => Q z.2 - Q v) :=
    ((model.continuous.comp continuous_snd).sub continuous_const).stronglyMeasurable
  have hfm := (S.fastError_continuous m).stronglyMeasurable
  refine ⟨(integrable_map_measure (g := fun z : Joint dx dy => Q z.2 - Q v)
      hgm.aestronglyMeasurable measurable_fst.aemeasurable).mp hg,
    (integrable_map_measure (g := S.fastError m) hfm.aestronglyMeasurable measurable_fst.aemeasurable).mp hf, ?_, ?_⟩
  · rw [integral_map measurable_fst.aemeasurable hgm.aestronglyMeasurable] at hgb
    exact hgb
  · rw [integral_map measurable_fst.aemeasurable hfm.aestronglyMeasurable] at hfb
    exact hfb

end SCObjective
end FreshGradientMinimax
