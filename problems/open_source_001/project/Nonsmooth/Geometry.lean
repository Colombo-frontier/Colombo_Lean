import Nonsmooth.Chord
import Mathlib.Analysis.Normed.Module.Convex

open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Exactly the two inequalities in the manuscript, restricted to the closed ball. -/
structure BallObjective (L μ R : ℝ) (f : E → ℝ) : Prop where
  lipschitz : ∀ x, ‖x‖ ≤ R → ∀ y, ‖y‖ ≤ R → |f x - f y| ≤ L * ‖x - y‖
  strong : StrongConvexOn (Metric.closedBall (0 : E) R) μ f

theorem unit_line_norm {u : E} (hu : ‖u‖ = 1) (t : ℝ) : ‖t • u‖ = |t| := by
  simp [norm_smul, hu, Real.norm_eq_abs]

theorem restrict_unit_line {L μ R : ℝ} {f : E → ℝ} (hf : BallObjective L μ R f)
    {u : E} (hu : ‖u‖ = 1) : IntervalObjective L μ R (fun t => f (t • u)) := by
  have hn (t : ℝ) (ht : t ∈ Set.Icc (-R) R) : ‖t • u‖ ≤ R := by
    rw [unit_line_norm hu]
    exact abs_le.mpr ht
  refine ⟨?_, ?_⟩
  · intro x hx y hy
    have h := hf.lipschitz (x • u) (hn x hx) (y • u) (hn y hy)
    simpa only [← sub_smul, unit_line_norm hu] using h
  · apply strongConvexOn_iff_convex.mpr
    have hc := strongConvexOn_iff_convex.mp hf.strong
    refine ⟨convex_Icc (-R) R, ?_⟩
    intro x hx y hy a b ha hb hab
    have h := hc.2 (by simpa using hn x hx) (by simpa using hn y hy) ha hb hab
    have hid : (a * x + b * y) • u = a • (x • u) + b • (y • u) := by
      simp [add_smul, mul_smul]
    simp only [smul_eq_mul, Real.norm_eq_abs, sq_abs]
    rw [← hid] at h
    simpa only [unit_line_norm hu, smul_eq_mul, sq_abs] using h

theorem ball_class_boundary_necessary {L μ R : ℝ} {f : E → ℝ}
    (hf : BallObjective L μ R f) (hμ : 0 < μ) (hR : 0 < R)
    {u : E} (hu : ‖u‖ = 1) : μ * R ≤ L :=
  class_boundary_necessary (restrict_unit_line hf hu) hμ hR

theorem ball_minimizer_localization {L μ R : ℝ} {f : E → ℝ}
    (hf : BallObjective L μ R f) (hμ : 0 < μ) (hR : 0 < R)
    (hg : 0 ≤ gap L μ R) {x : E} (hx : ‖x‖ ≤ R)
    (hmin : ∀ y, ‖y‖ ≤ R → f x ≤ f y) :
    ‖x‖ ≤ radius (gap L μ R) μ R := by
  by_cases hx0 : x = 0
  · simpa [hx0] using radius_nonneg hg hμ hR.le
  · have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    let u := ‖x‖⁻¹ • x
    have hu : ‖u‖ = 1 := by simp [u, norm_smul, abs_of_pos hr, hr.ne']
    have hid : ‖x‖ • u = x := by simp [u, smul_smul, hr.ne']
    apply positive_minimizer_localization (restrict_unit_line hf hu) hμ hR hr hx
    intro t ht
    rw [hid]
    apply hmin
    rw [unit_line_norm hu]
    exact abs_le.mpr ht

theorem ball_center_regret_bound {L μ R : ℝ} {f : E → ℝ}
    (hf : BallObjective L μ R f) (hμ : 0 < μ) (hR : 0 < R)
    (hg : 0 ≤ gap L μ R) {x : E} (hx : ‖x‖ ≤ R) :
    f 0 - f x ≤ energy (gap L μ R) μ R := by
  by_cases hx0 : x = 0
  · simpa [hx0] using energy_nonneg hg hμ hR.le
  · have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    let u := ‖x‖⁻¹ • x
    have hu : ‖u‖ = 1 := by simp [u, norm_smul, abs_of_pos hr, hr.ne']
    have hid : ‖x‖ • u = x := by simp [u, smul_smul, hr.ne']
    have h := center_regret_bound (restrict_unit_line hf hu) hμ hR hr.le hx
    simpa [hid] using h

def extremal (μ g : ℝ) (u x : E) : ℝ := μ / 2 * ‖x‖ ^ 2 - g * ⟪u, x⟫_ℝ

theorem extremal_strong (μ g R : ℝ) (u : E) :
    StrongConvexOn (Metric.closedBall (0 : E) R) μ (extremal μ g u) := by
  apply strongConvexOn_iff_convex.mpr
  refine ⟨convex_closedBall (0 : E) R, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [extremal, inner_add_right, inner_smul_right, smul_eq_mul]
  ring_nf
  exact le_rfl

theorem extremal_lipschitz {μ g R : ℝ} (hμ : 0 < μ) (hg : 0 ≤ g)
    {u : E} (hu : ‖u‖ = 1) {x y : E} (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) :
    |extremal μ g u x - extremal μ g u y| ≤ (μ * R + g) * ‖x - y‖ := by
  have hid : extremal μ g u x - extremal μ g u y =
      ⟪(μ / 2) • (x + y) - g • u, x - y⟫_ℝ := by
    simp only [extremal, inner_sub_left, real_inner_smul_left, inner_add_left,
      inner_sub_right, real_inner_self_eq_norm_sq]
    rw [real_inner_comm y x]
    ring
  have hn : ‖(μ / 2) • (x + y) - g • u‖ ≤ μ * R + g := by
    calc
      _ ≤ ‖(μ / 2) • (x + y)‖ + ‖g • u‖ := norm_sub_le _ _
      _ = μ / 2 * ‖x + y‖ + g := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (by positivity : 0 ≤ μ / 2), abs_of_nonneg hg, hu, mul_one]
      _ ≤ μ / 2 * (‖x‖ + ‖y‖) + g := by gcongr; exact norm_add_le _ _
      _ ≤ μ * R + g := by nlinarith
  rw [hid]
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right hn (norm_nonneg _))

theorem extremal_mem_class {μ g R : ℝ} (hμ : 0 < μ) (hg : 0 ≤ g)
    {u : E} (hu : ‖u‖ = 1) : BallObjective (g + μ * R) μ R (extremal μ g u) := by
  refine ⟨?_, extremal_strong μ g R u⟩
  intro x hx y hy
  simpa [add_comm] using extremal_lipschitz hμ hg hu hx hy

theorem extremal_minimum {μ g R : ℝ} (hμ : 0 < μ) (hg : 0 ≤ g) (hR : 0 ≤ R)
    {u : E} (hu : ‖u‖ = 1) :
    extremal μ g u (radius g μ R • u) = -energy g μ R ∧
      ∀ x, ‖x‖ ≤ R → -energy g μ R ≤ extremal μ g u x := by
  constructor
  · simp only [extremal, unit_line_norm hu, inner_smul_right,
      real_inner_self_eq_norm_sq, hu, one_pow, mul_one, sq_abs, energy]
    ring
  · intro x hx
    have hi : ⟪u, x⟫_ℝ ≤ ‖x‖ := by
      simpa [hu] using real_inner_le_norm u x
    have hm := mul_le_mul_of_nonneg_left hi hg
    have hr := radial_maximizer hg hμ hR (norm_nonneg x) hx
    unfold extremal
    nlinarith

/-- The center's bound and localization radius are attained by an actual admissible objective. -/
theorem extremal_attains_bounds {μ g R : ℝ} (hμ : 0 < μ) (hg : 0 ≤ g) (hR : 0 ≤ R)
    {u : E} (hu : ‖u‖ = 1) :
    BallObjective (g + μ * R) μ R (extremal μ g u) ∧
    ‖radius g μ R • u‖ = radius g μ R ∧
    ‖radius g μ R • u‖ ≤ R ∧
    extremal μ g u 0 - extremal μ g u (radius g μ R • u) = energy g μ R := by
  have hr0 := radius_nonneg hg hμ hR
  have hnorm : ‖radius g μ R • u‖ = radius g μ R := by
    rw [unit_line_norm hu, abs_of_nonneg hr0]
  refine ⟨extremal_mem_class hμ hg hu, hnorm, ?_, ?_⟩
  · rw [hnorm]
    exact radius_le_R g μ R
  · rw [(extremal_minimum hμ hg hR hu).1]
    simp [extremal]

theorem signed_pair_average (μ g U : ℝ) (u x : E) :
    ((extremal μ g u x + U) + (extremal μ g (-u) x + U)) / 2 =
      μ / 2 * ‖x‖ ^ 2 + U := by
  simp only [extremal, inner_neg_left]
  ring

end
end Nonsmooth
