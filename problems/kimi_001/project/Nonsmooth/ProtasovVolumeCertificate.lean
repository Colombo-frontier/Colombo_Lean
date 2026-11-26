import Nonsmooth.ProtasovTransfer
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

open MeasureTheory MeasureTheory.Measure Set
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- Contracting a convex domain toward a minimizer produces a relative sublevel set. -/
theorem convex_contraction_sublevel {G : Set E} {f : E → ℝ}
    (hf : ConvexOn ℝ G f) {x : E} (hx : x ∈ G) {M t : ℝ}
    (hM : ∀ y ∈ G, f y ≤ M) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (fun y => (1 - t) • x + t • y) '' G ⊆
      {z | z ∈ G ∧ f z ≤ f x + t * (M - f x)} := by
  rintro z ⟨y, hy, rfl⟩
  have hab : 1 - t + t = 1 := by ring
  refine ⟨hf.1 hx hy (sub_nonneg.mpr ht1) ht hab, ?_⟩
  have hc := hf.2 hx hy (sub_nonneg.mpr ht1) ht hab
  simp only [smul_eq_mul] at hc
  nlinarith [mul_le_mul_of_nonneg_left (hM y hy) ht]

theorem addHaar_convex_contraction (μ : Measure E) [IsAddHaarMeasure μ]
    (G : Set E) (x : E) {t : ℝ} (ht : 0 ≤ t) :
    μ ((fun y => (1 - t) • x + t • y) '' G) =
      ENNReal.ofReal (t ^ Module.finrank ℝ E) * μ G := by
  have hmap : (fun y => (1 - t) • x + t • y) = AffineMap.homothety x t := by
    funext y
    simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add,
      sub_smul, one_smul, smul_sub]
    abel
  rw [hmap, addHaar_image_homothety, abs_of_nonneg (pow_nonneg ht _)]

/-- A retained region containing every point better than the output certifies
relative accuracy once its volume falls below the contracted-domain volume. -/
theorem convex_relative_error_of_small_retained_volume
    (μ : Measure E) [IsAddHaarMeasure μ] {G K : Set E} {f : E → ℝ}
    (hf : ConvexOn ℝ G f) {x y : E} (hx : x ∈ G) {M t : ℝ}
    (hM : ∀ z ∈ G, f z ≤ M) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hkeep : ∀ z ∈ G, f z < f y → z ∈ K)
    (hvol : μ K < ENNReal.ofReal (t ^ Module.finrank ℝ E) * μ G) :
    f y - f x ≤ t * (M - f x) := by
  by_contra h
  have herr : f x + t * (M - f x) < f y := by linarith
  have hs : (fun z => (1 - t) • x + t • z) '' G ⊆ K := by
    intro z hz
    obtain ⟨hzG, hzf⟩ := convex_contraction_sublevel hf hx hM ht ht1 hz
    exact hkeep z hzG (hzf.trans_lt herr)
  have hm := measure_mono (μ := μ) hs
  rw [addHaar_convex_contraction μ G x ht] at hm
  exact (not_lt_of_ge hm) hvol

theorem ball_relative_error_of_small_retained_volume
    (μ : Measure E) [IsAddHaarMeasure μ] {R t : ℝ} (hR : 0 ≤ R)
    {f : E → ℝ} (hcont : ContinuousOn f (Metric.closedBall 0 R))
    (hconv : ConvexOn ℝ (Metric.closedBall 0 R) f)
    (y : Feasible E R) (K : Set E) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hkeep : ∀ z ∈ Metric.closedBall (0 : E) R, f z < f y.val → z ∈ K)
    (hvol : μ K < ENNReal.ofReal (t ^ Module.finrank ℝ E) *
      μ (Metric.closedBall (0 : E) R)) :
    f y.val - minimumValue R f ≤ t * (maximumValue R f - minimumValue R f) := by
  have hne : (Metric.closedBall (0 : E) R).Nonempty := ⟨0, by simpa using hR⟩
  obtain ⟨xmin, hxmin, hmin⟩ := (isCompact_closedBall (0 : E) R).exists_isMinOn hne hcont
  obtain ⟨xmax, hxmax, hmax⟩ := (isCompact_closedBall (0 : E) R).exists_isMaxOn hne hcont
  have hxmin' : ‖xmin‖ ≤ R := by simpa using hxmin
  have hxmax' : ‖xmax‖ ≤ R := by simpa using hxmax
  have hmin' : ∀ z, ‖z‖ ≤ R → f xmin ≤ f z := fun z hz => hmin (by simpa using hz)
  have hmax' : ∀ z, ‖z‖ ≤ R → f z ≤ f xmax := fun z hz => hmax (by simpa using hz)
  rw [minimumValue_eq hxmin' hmin', maximumValue_eq hxmax' hmax']
  exact convex_relative_error_of_small_retained_volume μ hconv hxmin
    (fun z hz => hmax hz) ht ht1 hkeep hvol

end
end Nonsmooth
