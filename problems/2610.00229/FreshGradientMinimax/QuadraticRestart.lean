import FreshGradientMinimax.QuadraticValue

/-! The recursive quadratic update and the unconditional 69e warm start
bound in F.5. Its coefficient can be correlated with the current iterate;
the proof uses only the two previous unconditional accuracy bounds. -/

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
variable {dx dy : ℕ}

def quadraticAdvance (w : ℝ) (z : Euclid dy × Joint dx dy) : Euclid dy × Joint dx dy :=
  (z.1 + w • z.2.2, z.2)

theorem quadraticAdvance_continuous (w : ℝ) : Continuous (quadraticAdvance (dx := dx) (dy := dy) w) :=
  (continuous_fst.add (continuous_const.smul continuous_snd.snd)).prodMk continuous_snd

namespace SCObjective
variable {ℓ μ α : ℝ} (S : SCObjective dx dy ℓ μ α)

def dualQuadraticGap (hfast : ℓ / 4 ≤ α) (a : ℝ) (ha : 0 ≤ a) (z : Euclid dy × Joint dx dy) : ℝ :=
  quadraticFamily S.effectiveValue a z.1 z.2.2 -
    quadraticFamily S.effectiveValue a z.1 (S.dualQuadraticMin hfast a ha z.1)

def dualQuadraticEnergy (hfast : ℓ / 4 ≤ α) (a : ℝ) (ha : 0 ≤ a) : Euclid dy × Joint dx dy → ℝ :=
  S.parameterEnergy (fun z => quadraticFamily S.effectiveValue a z.1 z.2) (μ + a)
    (S.dualQuadraticMin hfast a ha)

theorem dualQuadraticEnergy_measurable (hfast : ℓ / 4 ≤ α) (a : ℝ) (ha : 0 ≤ a) :
    Measurable (S.dualQuadraticEnergy hfast a ha) :=
  S.parameterEnergy_measurable _ ((S.effective_model hfast).quadraticFamily_joint_continuous a).measurable
    _ _ (S.dualQuadraticMin_continuous hfast a ha).measurable

theorem dualQuadraticEnergy_nonneg (hfast : ℓ / 4 ≤ α) (a : ℝ) (ha : 0 ≤ a)
    (z : Euclid dy × Joint dx dy) : 0 ≤ S.dualQuadraticEnergy hfast a ha z :=
  S.solverEnergy_nonneg (add_nonneg S.μ_pos.le ha) _ (S.dualQuadraticMin_minimizes hfast a ha z.1) z.2

theorem quadratic_advance_gap (hfast : ℓ / 4 ≤ α) (a w : ℝ) (ha : 0 ≤ a) (hw : 0 ≤ w)
    (z : Euclid dy × Joint dx dy) :
    S.dualQuadraticGap hfast (a + w) (add_nonneg ha hw) (quadraticAdvance w z) ≤
      S.dualQuadraticGap hfast a ha z := by
  let vnew := S.dualQuadraticMin hfast (a + w) (add_nonneg ha hw) (z.1 + w • z.2.2)
  have hmin := S.dualQuadraticMin_minimizes hfast a ha z.1 vnew
  have hp : 0 ≤ w / 2 * ‖vnew - z.2.2‖ ^ 2 := by positivity
  change quadraticFamily S.effectiveValue (a + w) (z.1 + w • z.2.2) z.2.2 -
    quadraticFamily S.effectiveValue (a + w) (z.1 + w • z.2.2) vnew ≤ _
  rw [quadraticFamily_increment, quadraticFamily_increment]
  simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero]
  dsimp only [dualQuadraticGap]
  linarith

theorem quadratic_restart_pointwise (hfast : ℓ / 4 ≤ α) (a : ℝ) (ha : 0 ≤ a)
    (z : Euclid dy × Joint dx dy) :
    S.dualQuadraticEnergy hfast (a + (μ + a)) (add_nonneg ha (add_nonneg S.μ_pos.le ha))
        (quadraticAdvance (μ + a) z) ≤
      65 * S.dualQuadraticGap hfast a ha z + 4 * S.fastError (μ + a) z.2 := by
  let anew := a + (μ + a)
  have hanew : 0 ≤ anew := add_nonneg ha (add_nonneg S.μ_pos.le ha)
  let bnew := z.1 + (μ + a) • z.2.2
  let vnew := S.dualQuadraticMin hfast anew hanew bnew
  let Qnew := quadraticFamily S.effectiveValue anew bnew
  have hgap := ((S.dualQuadratic_model hfast anew bnew).gap_quadratic_bounds vnew
    (S.dualQuadraticMin_minimizes hfast anew hanew bnew) z.2.2).1
  have htri := S.solverEnergy_triangle (Q := Qnew) (add_nonneg S.μ_pos.le hanew) hfast vnew z.2
  have hle := S.quadratic_advance_gap hfast a (μ + a) ha (add_nonneg S.μ_pos.le ha) z
  have hfastEq : S.fastError (μ + anew) z.2 = 2 * S.fastError (μ + a) z.2 := by
    dsimp [fastError, anew]
    ring
  rw [hfastEq] at htri
  change S.solverEnergy Qnew (μ + anew) vnew z.2 ≤ _
  change Qnew z.2.2 - Qnew vnew ≤ S.dualQuadraticGap hfast a ha z at hle
  change (μ + anew) / 2 * ‖z.2.2 - vnew‖ ^ 2 ≤ Qnew z.2.2 - Qnew vnew at hgap
  have hd : 32 * (μ + anew) * ‖z.2.2 - vnew‖ ^ 2 ≤ 64 * (Qnew z.2.2 - Qnew vnew) := by
    convert mul_le_mul_of_nonneg_left hgap (by norm_num : (0 : ℝ) ≤ 64) using 1
    ring
  calc
    S.solverEnergy Qnew (μ + anew) vnew z.2 ≤
      65 * (Qnew z.2.2 - Qnew vnew) + 4 * S.fastError (μ + a) z.2 := by linarith only [htri, hd]
    _ ≤ _ := by linarith only [hle]

theorem quadratic_restart_mean (hfast : ℓ / 4 ≤ α) (a : ℝ) (ha : 0 ≤ a)
    (ν : Measure (Euclid dy × Joint dx dy)) [IsProbabilityMeasure ν] (e : ℝ)
    (hg : Integrable (S.dualQuadraticGap hfast a ha) ν)
    (hf : Integrable (fun z : Euclid dy × Joint dx dy => S.fastError (μ + a) z.2) ν)
    (hgap : (∫ z, S.dualQuadraticGap hfast a ha z ∂ν) ≤ e)
    (hfastError : (∫ z, S.fastError (μ + a) z.2 ∂ν) ≤ e) :
    Integrable (S.dualQuadraticEnergy hfast (a + (μ + a)) (add_nonneg ha (add_nonneg S.μ_pos.le ha)))
      (ν.map (quadraticAdvance (μ + a))) ∧
    (∫ z, S.dualQuadraticEnergy hfast (a + (μ + a)) (add_nonneg ha (add_nonneg S.μ_pos.le ha)) z
      ∂ν.map (quadraticAdvance (μ + a))) ≤ 69 * e := by
  let anew := a + (μ + a)
  have hanew : 0 ≤ anew := add_nonneg ha (add_nonneg S.μ_pos.le ha)
  have hmeas := (S.dualQuadraticEnergy_measurable hfast anew hanew).stronglyMeasurable
  have hadv := (quadraticAdvance_continuous (dx := dx) (dy := dy) (μ + a)).measurable
  have hW := (hg.const_mul 65).add (hf.const_mul 4)
  have hi : Integrable (fun z => S.dualQuadraticEnergy hfast anew hanew (quadraticAdvance (μ + a) z)) ν := by
    apply hW.mono' (hmeas.measurable.comp hadv).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro z
    change ‖S.dualQuadraticEnergy hfast anew hanew (quadraticAdvance (μ + a) z)‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (S.dualQuadraticEnergy_nonneg hfast anew hanew _)]
    exact S.quadratic_restart_pointwise hfast a ha z
  refine ⟨(integrable_map_measure hmeas.aestronglyMeasurable hadv.aemeasurable).mpr hi, ?_⟩
  rw [integral_map hadv.aemeasurable hmeas.aestronglyMeasurable]
  have h := integral_mono hi hW (S.quadratic_restart_pointwise hfast a ha)
  dsimp only [Pi.add_apply] at h
  rw [integral_add (hg.const_mul 65) (hf.const_mul 4), integral_const_mul, integral_const_mul] at h
  linarith

theorem quadraticValueProgram_restart {σ : ℝ} (O : FreshOracle S.toNCObjective σ)
    (hαℓ : α ≤ ℓ) (hfast : ℓ / 4 ≤ α) {a e E₀ : ℝ} (ha : 0 ≤ a) (he : 0 < e)
    (ν : Measure (Euclid dy × Joint dx dy)) [IsProbabilityMeasure ν]
    (hInit : Integrable (S.dualQuadraticEnergy hfast a ha) ν)
    (hEnergy : (∫ z, S.dualQuadraticEnergy hfast a ha z ∂ν) ≤ E₀) :
    Integrable (S.dualQuadraticEnergy hfast (a + (μ + a)) (add_nonneg ha (add_nonneg S.μ_pos.le ha)))
      ((((quadraticValueProgram dx dy ℓ α σ μ a e E₀).originalKernel O.kernel ∘ₘ ν).map Prod.fst).map
        (quadraticAdvance (μ + a))) ∧
    (∫ z, S.dualQuadraticEnergy hfast (a + (μ + a)) (add_nonneg ha (add_nonneg S.μ_pos.le ha)) z
      ∂(((quadraticValueProgram dx dy ℓ α σ μ a e E₀).originalKernel O.kernel ∘ₘ ν).map Prod.fst).map
        (quadraticAdvance (μ + a))) ≤ 69 * e := by
  obtain ⟨hg, hf, hgb, hfb⟩ := S.quadraticValueProgram_accuracy O hαℓ hfast ha he ν hInit hEnergy
  have hgm : StronglyMeasurable (S.dualQuadraticGap hfast a ha) :=
    (parameterGap_measurable _ ((S.effective_model hfast).quadraticFamily_joint_continuous a).measurable
      _ (S.dualQuadraticMin_continuous hfast a ha).measurable).stronglyMeasurable
  have hfm : StronglyMeasurable (fun z : Euclid dy × Joint dx dy => S.fastError (μ + a) z.2) :=
    ((S.fastError_continuous _).measurable.comp measurable_snd).stronglyMeasurable
  have hgi := (integrable_map_measure (g := S.dualQuadraticGap hfast a ha)
    hgm.aestronglyMeasurable measurable_fst.aemeasurable).mpr hg
  have hfi := (integrable_map_measure (g := fun z : Euclid dy × Joint dx dy => S.fastError (μ + a) z.2)
    hfm.aestronglyMeasurable measurable_fst.aemeasurable).mpr hf
  have hgbi : (∫ z, S.dualQuadraticGap hfast a ha z
      ∂((quadraticValueProgram dx dy ℓ α σ μ a e E₀).originalKernel O.kernel ∘ₘ ν).map Prod.fst) ≤ e := by
    rw [integral_map measurable_fst.aemeasurable hgm.aestronglyMeasurable]
    exact hgb
  have hfbi : (∫ z : Euclid dy × Joint dx dy, S.fastError (μ + a) z.2
      ∂((quadraticValueProgram dx dy ℓ α σ μ a e E₀).originalKernel O.kernel ∘ₘ ν).map Prod.fst) ≤ e := by
    rw [integral_map measurable_fst.aemeasurable hfm.aestronglyMeasurable]
    exact hfb
  rw [OracleProgram.originalKernel_eq_law] at hgi hfi hgbi hfbi ⊢
  letI : IsProbabilityMeasure (((quadraticValueProgram dx dy ℓ α σ μ a e E₀).lawKernel O.kernel ∘ₘ ν).map Prod.fst) :=
    isProbabilityMeasure_map measurable_fst.aemeasurable
  exact S.quadratic_restart_mean hfast a ha _ e hgi hfi hgbi hfbi

end SCObjective
end FreshGradientMinimax
