import FreshGradientMinimax.SmoothRamp
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-! The convex smooth maximum from Appendix A.1. The exact flat regions
and the derivative formula hold globally, including the interfaces. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

def smoothMaximum (η a b : ℝ) : ℝ := a + smoothRamp η (b - a)

theorem smoothMaximum_left {η a b : ℝ} (hb : b ≤ a) : smoothMaximum η a b = a := by
  simp [smoothMaximum, smoothRamp_zero (sub_nonpos.mpr hb)]

theorem smoothMaximum_right {η a b : ℝ} (hη : 0 < η) (hb : η ≤ b - a) :
    smoothMaximum η a b = b - η / 2 := by
  rw [smoothMaximum, smoothRamp_linear hη hb]
  ring

theorem smoothMaximum_ge_left {η : ℝ} (hη : 0 < η) (a b : ℝ) : a ≤ smoothMaximum η a b := by
  exact le_add_of_nonneg_right (smoothRamp_nonneg hη (b - a))

theorem smoothMaximum_derivative_left {η : ℝ} (hη : 0 < η) (a b : ℝ) :
    HasDerivAt (fun x => smoothMaximum η x b) (1 - smoothRampSlope η (b - a)) a := by
  convert (hasDerivAt_id a).add ((smoothRamp_derivative hη (b - a)).comp a
    ((hasDerivAt_const a b).sub (hasDerivAt_id a))) using 1
  ring

theorem smoothMaximum_derivative_right {η : ℝ} (hη : 0 < η) (a b : ℝ) :
    HasDerivAt (smoothMaximum η a) (smoothRampSlope η (b - a)) b := by
  convert (hasDerivAt_const b a).add ((smoothRamp_derivative hη (b - a)).comp b
    ((hasDerivAt_id b).sub_const a)) using 1
  ring

theorem smoothMaximum_monotone_left {η : ℝ} (hη : 0 < η) (b : ℝ) :
    Monotone (fun a => smoothMaximum η a b) := by
  apply monotone_of_hasDerivAt_nonneg (fun a => smoothMaximum_derivative_left hη a b)
  intro a
  change 0 ≤ 1 - smoothRampSlope η (b - a)
  linarith [(smoothRampSlope_bounds hη (b - a)).2]

theorem smoothMaximum_monotone_right {η : ℝ} (hη : 0 < η) (a : ℝ) :
    Monotone (smoothMaximum η a) :=
  monotone_of_hasDerivAt_nonneg (fun b => smoothMaximum_derivative_right hη a b)
    (fun b => (smoothRampSlope_bounds hη (b - a)).1)

theorem smoothMaximum_convex {η : ℝ} (hη : 0 < η) :
    ConvexOn ℝ Set.univ (fun z : ℝ × ℝ => smoothMaximum η z.1 z.2) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have h := (smoothRamp_convex hη).2 (Set.mem_univ (x.2 - x.1))
    (Set.mem_univ (y.2 - y.1)) ha hb hab
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    smoothMaximum] at h ⊢
  have he : a * x.2 + b * y.2 - (a * x.1 + b * y.1) =
      a * (x.2 - x.1) + b * (y.2 - y.1) := by ring
  rw [he]
  linarith

theorem smoothMaximum_contDiff {η : ℝ} (hη : 0 < η) :
    ContDiff ℝ 1 (fun z : ℝ × ℝ => smoothMaximum η z.1 z.2) :=
  contDiff_fst.add ((smoothRamp_contDiff hη).comp (contDiff_snd.sub contDiff_fst))

theorem smoothMaximum_comp_hasFDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {η : ℝ} (hη : 0 < η) {f g : E → ℝ} {f' g' : E →L[ℝ] ℝ} {x : E}
    (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x) :
    HasFDerivAt (fun z => smoothMaximum η (f z) (g z))
      ((1 - smoothRampSlope η (g x - f x)) • f' + smoothRampSlope η (g x - f x) • g') x := by
  convert hf.add ((smoothRamp_derivative hη (g x - f x)).comp_hasFDerivAt x (hg.sub hf)) using 1
  ext v
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, smul_eq_mul]
  ring

theorem smoothMaximum_comp_convex {E : Type*} [AddCommGroup E] [Module ℝ E]
    {η : ℝ} (hη : 0 < η) {S : Set E} {f g : E → ℝ}
    (hf : ConvexOn ℝ S f) (hg : ConvexOn ℝ S g) :
    ConvexOn ℝ S (fun x => smoothMaximum η (f x) (g x)) := by
  refine ⟨hf.1, ?_⟩
  intro x hx y hy a b ha hb hab
  have h1 := smoothMaximum_monotone_left hη (g (a • x + b • y)) (hf.2 hx hy ha hb hab)
  have h2 := smoothMaximum_monotone_right hη (a • f x + b • f y) (hg.2 hx hy ha hb hab)
  have h3 := (smoothMaximum_convex hη).2 (Set.mem_univ (f x, g x))
    (Set.mem_univ (f y, g y)) ha hb hab
  exact (h1.trans h2).trans h3

end FreshGradientMinimax
