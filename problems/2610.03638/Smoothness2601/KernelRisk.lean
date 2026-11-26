import Smoothness2601.FixedFrameSimulation
import Smoothness2601.PrefixExecution

/-! Transfer the proved pathwise hidden-output event to the article's actual
kernel expected gradient norm, including divergent expectations. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace Smoothness2601.PrefixSimulator
open MeasureTheory ProbabilityTheory
open Bilevel EuclideanGaussian ProjectionPosterior PrimitiveGeometry IndependentDraws
open scoped RealInnerProductSpace ENNReal

variable {d T : ℕ} {b : Budgets}
variable (A : Adaptive.Algorithm (Space d) ℝ)
variable (reply : Frame d T → Adaptive.Query (Space d) ℝ → Bool → Joint (Space d) ℝ)

theorem expectedNorm_of_hidden_output (U : Frame d T)
    (hr : Measurable (fun z : Adaptive.Query (Space d) ℝ × Bool => reply U z.1 z.2))
    {P : Population (X := Space d) (Y := ℝ) b} (O : Adaptive.Oracle P Unit)
    (ν : Measure Bool) [IsProbabilityMeasure ν]
    (hlaw : ∀ q, O.law (q,()) = ν.map (fun coin => (reply U q coin,())))
    (outPoint : Space d → Space d) (δ : ℝ) (N : ℕ) (input : Space d × ℝ)
    {margin : ℝ} (_hmargin : 0 ≤ margin)
    (hbarrier : ∀ x, (∃ i : Fin T, |⟪outPoint x,U i⟫| < δ) → margin ≤ ‖gradient P.objective x‖)
    (hlarge : (1/2 : ℝ≥0∞) ≤ ∫⁻ m, ∫⁻ c,
      if hiddenOutput A reply (coinSequence N c) outPoint δ m N U then (1:ℝ≥0∞) else 0
      ∂law ν N ∂A.initialLaw input) :
    ENNReal.ofReal (margin/2) ≤ Adaptive.expectedNorm A O N () input.1 input.2 := by
  have hg : Measurable (fun x => (‖gradient P.objective x‖₊ : ℝ≥0∞)) :=
    (P.primitive.gradient_hyperobjective_lipschitz P.primitive.canonicalResponse).continuous.measurable.nnnorm.coe_nnreal_ennreal
  have hrisk : Measurable (fun z : A.Memory × Draws Bool N =>
      (‖gradient P.objective (A.output (realState A reply (coinSequence N z.2) z.1 U N))‖₊ : ℝ≥0∞)) := by
    have hh := hg.comp (A.output_measurable.comp
      (IndependentExecution.memoryRun_joint_measurable A (reply U) hr N))
    convert hh using 1
    funext z
    rw [realState_eq_independent_run]
    rfl
  have he : Adaptive.expectedNorm A O N () input.1 input.2 =
      ∫⁻ m, ∫⁻ c,
        (‖gradient P.objective (A.output (realState A reply (coinSequence N c) m U N))‖₊ : ℝ≥0∞)
        ∂law ν N ∂A.initialLaw input := by
    unfold Adaptive.expectedNorm
    rw [show (input.1,input.2) = input from Prod.eta input]
    rw [realState_lintegral_output A reply U hr O ν hlaw N input _ hg]
    exact lintegral_prod _ hrisk.aemeasurable
  rw [he]
  have hl := mul_le_mul_left' hlarge (ENNReal.ofReal margin)
  have hmul : ENNReal.ofReal (margin/2) = ENNReal.ofReal margin*(1/2 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2)]
    norm_num [div_eq_mul_inv]
  rw [hmul]
  apply hl.trans
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro m
  dsimp only
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro c
  dsimp only
  by_cases hh : hiddenOutput A reply (coinSequence N c) outPoint δ m N U
  · rw [if_pos hh,mul_one]
    have hb := ENNReal.ofReal_le_ofReal (hbarrier _ hh)
    simpa only [← coe_nnnorm,ENNReal.ofReal_coe_nnreal] using hb
  · rw [if_neg hh,mul_zero]
    exact zero_le _

end Smoothness2601.PrefixSimulator
