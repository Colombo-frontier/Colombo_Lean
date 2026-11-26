import ReadOnceProbability
import OracleRunMeasurable

open MeasureTheory ProbabilityTheory

namespace Task006.Full
namespace OracleAlgorithm

noncomputable section

variable {d N : ℕ} {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]

def queriedIndicator (A : OracleAlgorithm d N S) (F : Space d → Ω → ℝ)
    (seed : S) (h : ℕ) (tape : ℕ → Ω) : ℝ :=
  {tape | A.queriedBefore F tape seed h N}.indicator (fun _ => 1) tape

theorem queriedIndicator_measurable (A : OracleAlgorithm d N S) (F : Space d → Ω → ℝ)
    (hF : Measurable (Function.uncurry F)) (seed : S) (h : ℕ) :
    Measurable (A.queriedIndicator F seed h) := by
  exact measurable_const.indicator
    ((A.measurableSet_queriedBefore F hF h N).preimage
      (measurable_const.prodMk measurable_id))

theorem queriedIndicator_indep_coordinate (A : OracleAlgorithm d N S)
    (F : Space d → Ω → ℝ) (hF : Measurable (Function.uncurry F))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (seed : S) (h : ℕ) (z : Ω) :
    IndepFun (fun tape : ℕ → Ω => tape h) (A.queriedIndicator F seed h)
      (iidHandleLaw μ) := by
  classical
  have hm := (A.queriedIndicator_measurable F hF seed h).comp (measurable_restoreTape h z)
  have hi := (iid_coordinate_indep_offTape μ h).comp measurable_id hm
  have heq : (A.queriedIndicator F seed h) =
      (fun tape => A.queriedIndicator F seed h (restoreTape h z (offTape h tape))) := by
    funext tape
    rw [restore_offTape]
    have he := A.queriedBefore_update_iff F tape seed h z
    change (if A.queriedBefore F tape seed h N then (1 : ℝ) else 0) =
      (if A.queriedBefore F (Function.update tape h z) seed h N then (1 : ℝ) else 0)
    rw [he]
  rw [heq]
  exact hi

/-- Exact factorization for an adaptively selected handle. The status is
independent of whether the handle is ever queried, because selection occurs
before its first paid reply. -/
theorem queried_handle_factorization (A : OracleAlgorithm d N S)
    (F : Space d → Ω → ℝ) (hF : Measurable (Function.uncurry F))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (seed : S) (h : ℕ) (z : Ω)
    (w : Ω → ℝ) (hw : Measurable w) :
    (∫ tape, w (tape h) * A.queriedIndicator F seed h tape ∂iidHandleLaw μ) =
      (∫ x, w x ∂μ) * (iidHandleLaw μ).real {tape | A.queriedBefore F tape seed h N} := by
  have hi := (A.queriedIndicator_indep_coordinate F hF μ seed h z).comp hw measurable_id
  have hmarg : MeasurePreserving (fun tape : ℕ → Ω => tape h) (iidHandleLaw μ) μ :=
    ⟨measurable_pi_apply h, Measure.infinitePi_map_eval (fun _ : ℕ => μ) h⟩
  have hs : MeasurableSet {tape | A.queriedBefore F tape seed h N} :=
    (A.measurableSet_queriedBefore F hF h N).preimage
      (measurable_const.prodMk measurable_id)
  calc
    _ = (∫ tape, w (tape h) ∂iidHandleLaw μ) *
        (∫ tape, A.queriedIndicator F seed h tape ∂iidHandleLaw μ) :=
      hi.integral_fun_mul_eq_mul_integral
        (hw.comp (measurable_pi_apply h)).aestronglyMeasurable
        (A.queriedIndicator_measurable F hF seed h).aestronglyMeasurable
    _ = _ := by
      have hint : (∫ tape, w (tape h) ∂iidHandleLaw μ) = ∫ x, w x ∂μ := by
        rw [← integral_map (measurable_pi_apply h).aemeasurable hw.aestronglyMeasurable,
          hmarg.map_eq]
      rw [hint]
      change (∫ x, w x ∂μ) *
        (∫ tape, {tape | A.queriedBefore F tape seed h N}.indicator (fun _ => (1 : ℝ)) tape
          ∂iidHandleLaw μ) = _
      congr 1
      simpa only [smul_eq_mul, mul_one] using
        (integral_indicator_const (μ := iidHandleLaw μ) (1 : ℝ) hs)

end
end OracleAlgorithm
end Task006.Full
