import Bilevel.StochasticInner

/-! Elementary actual-integral error transfer, with integrability proved from L2. -/
noncomputable section
open MeasureTheory
namespace Bilevel.MSETransfer
variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace Ω] {ν : Measure Ω}

omit [InnerProductSpace ℝ E] in
theorem squared_triangle (u v w : E) : ‖u - w‖ ^ 2 ≤ 2 * ‖u - v‖ ^ 2 + 2 * ‖v - w‖ ^ 2 := by
  have ht := norm_sub_le_norm_sub_add_norm_sub u v w
  nlinarith only [ht, norm_nonneg (u - w), norm_nonneg (u - v), norm_nonneg (v - w),
    sq_nonneg (‖u - v‖ - ‖v - w‖)]

omit [InnerProductSpace ℝ E] in
theorem integral_triangle (u v w : Ω → E) (hu : MemLp u 2 ν) (hv : MemLp v 2 ν) (hw : MemLp w 2 ν) :
    (∫ ω, ‖u ω - w ω‖ ^ 2 ∂ν) ≤ 2 * (∫ ω, ‖u ω - v ω‖ ^ 2 ∂ν) + 2 * (∫ ω, ‖v ω - w ω‖ ^ 2 ∂ν) := by
  have hi : Integrable (fun ω => ‖u ω - w ω‖ ^ 2) ν :=
    (memLp_two_iff_integrable_sq_norm (hu.sub hw).aestronglyMeasurable).mp (hu.sub hw)
  have huv : Integrable (fun ω => ‖u ω - v ω‖ ^ 2) ν :=
    (memLp_two_iff_integrable_sq_norm (hu.sub hv).aestronglyMeasurable).mp (hu.sub hv)
  have hvw : Integrable (fun ω => ‖v ω - w ω‖ ^ 2) ν :=
    (memLp_two_iff_integrable_sq_norm (hv.sub hw).aestronglyMeasurable).mp (hv.sub hw)
  have hh := integral_mono hi ((huv.const_mul 2).add (hvw.const_mul 2)) (fun ω => squared_triangle (u ω) (v ω) (w ω))
  simpa only [Pi.add_apply, integral_add (huv.const_mul 2) (hvw.const_mul 2), integral_const_mul] using hh

omit [InnerProductSpace ℝ E] in
theorem deterministic_target [IsProbabilityMeasure ν] (u : Ω → E) (hu : MemLp u 2 ν) (v w : E) :
    (∫ ω, ‖u ω - w‖ ^ 2 ∂ν) ≤ 2 * (∫ ω, ‖u ω - v‖ ^ 2 ∂ν) + 2 * ‖v - w‖ ^ 2 := by
  simpa only [integral_const, measureReal_univ_eq_one, one_smul] using
    integral_triangle u (fun _ => v) (fun _ => w) hu (memLp_const v) (memLp_const w)

theorem linear_error (D : E →L[ℝ] E) (u v : Ω → E) (hu : MemLp u 2 ν) (hv : MemLp v 2 ν)
    (c : ℝ) (hc : 0 ≤ c) (hD : ‖D‖ ≤ c) :
    (∫ ω, ‖D (u ω) - D (v ω)‖ ^ 2 ∂ν) ≤ c ^ 2 * (∫ ω, ‖u ω - v ω‖ ^ 2 ∂ν) := by
  have hbase := hu.sub hv
  have hm := (D.comp_memLp' hu).sub (D.comp_memLp' hv)
  have hi : Integrable (fun ω => ‖D (u ω) - D (v ω)‖ ^ 2) ν :=
    (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
  have hb : Integrable (fun ω => ‖u ω - v ω‖ ^ 2) ν :=
    (memLp_two_iff_integrable_sq_norm hbase.aestronglyMeasurable).mp hbase
  have hh := integral_mono hi (hb.const_mul (c ^ 2)) (fun ω => ?_)
  · simpa only [integral_const_mul] using hh
  · rw [← map_sub, ← mul_pow]
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))).mpr
      ((D.le_opNorm _).trans (mul_le_mul_of_nonneg_right hD (norm_nonneg _)))

end Bilevel.MSETransfer
