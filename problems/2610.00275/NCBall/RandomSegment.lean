import NCBall.ClarkeSmooth
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod

/-! # Uniform segment sampling converts gradients into objective differences -/

noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace unitInterval
namespace NCBall

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem hasDerivAt_along_segment {f : E → ℝ} (hf : ContDiff ℝ 1 f) (x v : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (x + s • v)) ⟪gradient f (x + t • v), v⟫_ℝ t := by
  have hp : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    simpa only [zero_add, one_smul] using
      (hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const v)
  have hc := ((hf.differentiable le_rfl) (x + t • v)).hasGradientAt.hasFDerivAt.comp_hasDerivAt t hp
  simpa only [InnerProductSpace.toDual_apply] using hc

theorem interval_segment_gradient_integral {f : E → ℝ} (hf : ContDiff ℝ 1 f) (x v : E) :
    (∫ t in (0 : ℝ)..1, ⟪gradient f (x + t • v), v⟫_ℝ) = f (x + v) - f x := by
  have hg : Continuous (fun t : ℝ => ⟪gradient f (x + t • v), v⟫_ℝ) :=
    ((gradient_continuous_of_C1 hf).comp (continuous_const.add (continuous_id.smul continuous_const))).inner
      continuous_const
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_along_segment hf x v t) (hg.intervalIntegrable 0 1)
  simpa only [one_smul, zero_smul, add_zero] using hi

theorem unit_segment_gradient_integral {f : E → ℝ} (hf : ContDiff ℝ 1 f) (x v : E) :
    (∫ t : I, ⟪gradient f (x + (t : ℝ) • v), v⟫_ℝ) = f (x + v) - f x := by
  rw [unitInterval.volume_def,
    integral_subtype_comap measurableSet_Icc (fun t : ℝ => ⟪gradient f (x + t • v), v⟫_ℝ),
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  exact interval_segment_gradient_integral hf x v

theorem random_segment_descent {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [SFinite ν] {f : E → ℝ} (hf : ContDiff ℝ 1 f) (x v : Ω → E)
    (hi : Integrable (fun w : Ω × I => ⟪gradient f (x w.1 + (w.2 : ℝ) • v w.1), v w.1⟫_ℝ)
      (ν.prod volume)) :
    (∫ w : Ω × I, ⟪gradient f (x w.1 + (w.2 : ℝ) • v w.1), v w.1⟫_ℝ ∂ν.prod volume) =
      ∫ ω, (f (x ω + v ω) - f (x ω)) ∂ν := by
  rw [integral_prod _ hi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun ω => unit_segment_gradient_integral hf (x ω) (v ω))

theorem random_segment_integrable {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (ν : Measure Ω) [IsFiniteMeasure ν] {f : E → ℝ} (hf : ContDiff ℝ 1 f)
    {L D : ℝ} (hL : 0 ≤ L) (_hD : 0 ≤ D) (hgrad : ∀ y, ‖gradient f y‖ ≤ L)
    (x v : Ω → E) (hx : Measurable x) (hv : Measurable v) (hvbound : ∀ ω, ‖v ω‖ ≤ D) :
    Integrable (fun w : Ω × I => ⟪gradient f (x w.1 + (w.2 : ℝ) • v w.1), v w.1⟫_ℝ)
      (ν.prod volume) := by
  have hp : Measurable (fun w : Ω × I => x w.1 + (w.2 : ℝ) • v w.1) :=
    (hx.comp measurable_fst).add
      ((measurable_subtype_coe.comp measurable_snd).smul (hv.comp measurable_fst))
  have hm : Measurable (fun w : Ω × I => ⟪gradient f (x w.1 + (w.2 : ℝ) • v w.1), v w.1⟫_ℝ) :=
    continuous_inner.measurable.comp
      (((gradient_continuous_of_C1 hf).measurable.comp hp).prodMk (hv.comp measurable_fst))
  have hb (w : Ω × I) : ‖⟪gradient f (x w.1 + (w.2 : ℝ) • v w.1), v w.1⟫_ℝ‖ ≤ L * D :=
    (norm_inner_le_norm _ _).trans (mul_le_mul (hgrad _) (hvbound _) (norm_nonneg _) hL)
  have hLp : MemLp (fun w : Ω × I => ⟪gradient f (x w.1 + (w.2 : ℝ) • v w.1), v w.1⟫_ℝ)
      2 (ν.prod volume) := MemLp.of_bound hm.aestronglyMeasurable (L * D) (Filter.Eventually.of_forall hb)
  exact hLp.integrable (by norm_num)

end NCBall
