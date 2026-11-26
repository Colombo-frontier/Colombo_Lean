import FreshGradientMinimax.Objective
import FreshGradientMinimax.Proximal

/-! Strongly convex--strongly concave geometry with actual extrema. The saddle,
slice minima, and saddle gap are constructed from the objective assumptions.
These results contain no assumptions about a solver or its oracle complexity. -/

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace

def StrongConvexGradient {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (g : E → E) (α : ℝ) : Prop :=
  ∀ x z, f x + ⟪g x, z - x⟫_ℝ + α / 2 * ‖z - x‖ ^ 2 ≤ f z

theorem strong_convex_minimum_exists {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [ProperSpace E] {f : E → ℝ} {g : E → E} {α : ℝ}
    (hα : 0 < α) (hc : StrongConvexGradient f g α) (hf : Continuous f) :
    ∃ u, ∀ x, f u ≤ f x := by
  have hn : StrongConcaveGradient (fun x => -f x) (fun x => -g x) α := by
    intro x z
    have h := hc x z
    simp only [inner_neg_left]
    linarith
  obtain ⟨u, hu⟩ := strong_concave_maximum_exists hα hn hf.neg
  exact ⟨u, fun x => neg_le_neg_iff.mp (hu x)⟩

theorem gradient_zero_at_global_min {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {f : E → ℝ} {g : E → E} (u : E)
    (hd : HasFDerivAt f (innerSL ℝ (g u)) u) (hu : ∀ x, f u ≤ f x) : g u = 0 := by
  have hmin : IsLocalMin f u := Filter.Eventually.of_forall hu
  have he := hmin.hasFDerivAt_eq_zero hd
  have hv := congrArg (fun l : E →L[ℝ] ℝ => l (g u)) he
  simp only [innerSL_apply, ContinuousLinearMap.zero_apply, real_inner_self_eq_norm_sq] at hv
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg (g u)]

structure SCObjective (dx dy : ℕ) (ℓ μ α : ℝ) extends NCObjective dx dy ℓ μ where
  α_pos : 0 < α
  primal_strong : ∀ v, StrongConvexGradient (fun u => f u v) (fun u => gradX u v) α

namespace SCObjective
variable {dx dy : ℕ} {ℓ μ α : ℝ} (S : SCObjective dx dy ℓ μ α)

theorem value_strong : StrongConvexGradient S.toNCObjective.value
    S.toNCObjective.primalGradient α := by
  intro x z
  have h := S.primal_strong (S.toNCObjective.dualMax x) x z
  dsimp only at h
  rw [← S.toNCObjective.value_eq_max] at h
  exact h.trans (S.toNCObjective.le_value z _)

theorem saddle_primal_exists : ∃ u, ∀ x, S.toNCObjective.value u ≤ S.toNCObjective.value x := by
  exact strong_convex_minimum_exists S.α_pos S.value_strong
    (continuous_iff_continuousAt.mpr (fun x => (S.toNCObjective.value_hasFDerivAt x).continuousAt))

def saddleU : Euclid dx := Classical.choose S.saddle_primal_exists
def saddleV : Euclid dy := S.toNCObjective.dualMax S.saddleU

theorem saddleU_minimizes (u : Euclid dx) :
    S.toNCObjective.value S.saddleU ≤ S.toNCObjective.value u :=
  Classical.choose_spec S.saddle_primal_exists u

theorem saddle_gradX_zero : S.gradX S.saddleU S.saddleV = 0 :=
  gradient_zero_at_global_min S.saddleU (S.toNCObjective.value_hasFDerivAt S.saddleU)
    S.saddleU_minimizes

theorem saddle_gradY_zero : S.gradY S.saddleU S.saddleV = 0 :=
  S.toNCObjective.dual_gradient_zero S.saddleU

theorem saddle_left (v : Euclid dy) : S.f S.saddleU v ≤ S.f S.saddleU S.saddleV :=
  S.toNCObjective.le_dualMax S.saddleU v

theorem saddle_right (u : Euclid dx) : S.f S.saddleU S.saddleV ≤ S.f u S.saddleV := by
  have h := S.primal_strong S.saddleV S.saddleU u
  dsimp only at h
  rw [S.saddle_gradX_zero, inner_zero_left, add_zero] at h
  have hn : 0 ≤ α / 2 * ‖u - S.saddleU‖ ^ 2 := by have := S.α_pos; positivity
  linarith

/-- Strong monotonicity of the saddle operator follows from four support bounds. -/
theorem saddle_operator_monotone (u u' : Euclid dx) (v v' : Euclid dy) :
    α * ‖u - u'‖ ^ 2 + μ * ‖v - v'‖ ^ 2 ≤
      ⟪S.gradX u v - S.gradX u' v', u - u'⟫_ℝ -
      ⟪S.gradY u v - S.gradY u' v', v - v'⟫_ℝ := by
  have h1 := S.primal_strong v u u'
  have h2 := S.primal_strong v' u' u
  have h3 := S.dual_strong u v v'
  have h4 := S.dual_strong u' v' v
  rw [norm_sub_rev u' u] at h1
  rw [norm_sub_rev v' v] at h3
  have hi1 : ⟪S.gradX u v, u' - u⟫_ℝ = -⟪S.gradX u v, u - u'⟫_ℝ := by
    simp only [inner_sub_right]; ring
  have hi2 : ⟪S.gradY u v, v' - v⟫_ℝ = -⟪S.gradY u v, v - v'⟫_ℝ := by
    simp only [inner_sub_right]; ring
  rw [hi1] at h1
  rw [hi2] at h3
  rw [inner_sub_left, inner_sub_left]
  linarith

theorem stationary_saddle_unique (u : Euclid dx) (v : Euclid dy)
    (hx : S.gradX u v = 0) (hy : S.gradY u v = 0) : u = S.saddleU ∧ v = S.saddleV := by
  have h := S.saddle_operator_monotone u S.saddleU v S.saddleV
  simp only [hx, hy, S.saddle_gradX_zero, S.saddle_gradY_zero, sub_self, inner_zero_left] at h
  have ha := S.α_pos
  have hm := S.μ_pos
  have hxu : ‖u - S.saddleU‖ ^ 2 ≤ 0 := by
    have hn := mul_nonneg hm.le (sq_nonneg ‖v - S.saddleV‖)
    exact (mul_le_mul_left ha).mp (by nlinarith)
  have hyv : ‖v - S.saddleV‖ ^ 2 ≤ 0 := by
    have hn := mul_nonneg ha.le (sq_nonneg ‖u - S.saddleU‖)
    exact (mul_le_mul_left hm).mp (by nlinarith)
  constructor
  · exact sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [norm_nonneg (u - S.saddleU)]))
  · exact sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [norm_nonneg (v - S.saddleV)]))

theorem slice_minimum_exists (v : Euclid dy) : ∃ u, ∀ x, S.f u v ≤ S.f x v := by
  exact strong_convex_minimum_exists S.α_pos (S.primal_strong v)
    (continuous_iff_continuousAt.mpr (fun x => (S.toNCObjective.derivative_x x v).continuousAt))

def sliceMin (v : Euclid dy) : Euclid dx := Classical.choose (S.slice_minimum_exists v)
def dualValue (v : Euclid dy) : ℝ := sInf (Set.range (fun u => S.f u v))

theorem sliceMin_minimizes (v : Euclid dy) (u : Euclid dx) : S.f (S.sliceMin v) v ≤ S.f u v :=
  Classical.choose_spec (S.slice_minimum_exists v) u

theorem dualValue_eq_min (v : Euclid dy) : S.dualValue v = S.f (S.sliceMin v) v := by
  apply IsLeast.csInf_eq
  exact ⟨⟨S.sliceMin v, rfl⟩, by rintro _ ⟨u, rfl⟩; exact S.sliceMin_minimizes v u⟩

theorem dualValue_le (v : Euclid dy) (u : Euclid dx) : S.dualValue v ≤ S.f u v := by
  rw [S.dualValue_eq_min]
  exact S.sliceMin_minimizes v u

def gap (u : Euclid dx) (v : Euclid dy) : ℝ := S.toNCObjective.value u - S.dualValue v

theorem gap_nonneg (u : Euclid dx) (v : Euclid dy) : 0 ≤ S.gap u v := by
  have h1 := S.dualValue_le v u
  have h2 := S.toNCObjective.le_value u v
  unfold gap
  linarith

theorem gap_dominates_primal (u : Euclid dx) (v : Euclid dy) :
    S.toNCObjective.value u - S.toNCObjective.value S.saddleU ≤ S.gap u v := by
  have h1 := S.dualValue_le v S.saddleU
  have h2 := S.toNCObjective.le_value S.saddleU v
  unfold gap
  linarith

theorem gap_controls_distance (u : Euclid dx) (v : Euclid dy) :
    α * ‖u - S.saddleU‖ ^ 2 + μ * ‖v - S.saddleV‖ ^ 2 ≤ 2 * S.gap u v := by
  have h1 := S.primal_strong S.saddleV S.saddleU u
  have h2 := S.dual_strong S.saddleU S.saddleV v
  dsimp only at h1
  rw [S.saddle_gradX_zero, inner_zero_left, add_zero] at h1
  rw [S.saddle_gradY_zero, inner_zero_left, add_zero] at h2
  have h3 := S.dualValue_le v S.saddleU
  have h4 := S.toNCObjective.le_value u S.saddleV
  unfold gap
  linarith

theorem gap_le_residual (u : Euclid dx) (v : Euclid dy) :
    S.gap u v ≤ ‖S.gradX u v‖ ^ 2 / (2 * α) + ‖S.gradY u v‖ ^ 2 / (2 * μ) := by
  rw [gap, S.toNCObjective.value_eq_max, S.dualValue_eq_min]
  exact saddle_gap_certificate S.α_pos S.μ_pos u (S.sliceMin v) v
    (S.toNCObjective.dualMax u) (S.gradX u v) (S.gradY u v)
    (S.primal_strong v u (S.sliceMin v)) (S.dual_strong u v (S.toNCObjective.dualMax u))

end SCObjective
end FreshGradientMinimax
