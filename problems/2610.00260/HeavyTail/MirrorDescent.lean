import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic

/-!
# Bregman mirror updates from actual constrained minimization

The generator has genuine within-set Fréchet derivatives; one-sided boundary
behavior is therefore allowed. The first-order condition is derived from an
actual `IsMinOn` hypothesis on a convex set, using its positive tangent cone.
Convexity and the within derivative also prove nonnegativity of the divergence.
Neither the three-point inequality nor the finite telescope is an input.

Existence/measurability of the optimizer and the Gaussian-mixture entropy
instantiation are separate obligations and are not asserted here.
-/

noncomputable section
open Set
open scoped BigOperators

namespace HeavyTail

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def bregmanDivergence (H : E → ℝ) (dH : E → E →L[ℝ] ℝ) (q x : E) : ℝ :=
  H q - H x - dH x (q - x)

def mirrorStability (H : E → ℝ) (dH : E → E →L[ℝ] ℝ)
    (L : E →L[ℝ] ℝ) (x y : E) : ℝ :=
  -L y - bregmanDivergence H dH y x

theorem bregmanDivergence_self (H : E → ℝ) (dH : E → E →L[ℝ] ℝ) (x : E) :
    bregmanDivergence H dH x x = 0 := by
  simp [bregmanDivergence]

theorem bregman_three_point_identity (H : E → ℝ) (dH : E → E →L[ℝ] ℝ)
    (q x y : E) :
    bregmanDivergence H dH q y - bregmanDivergence H dH q x +
      bregmanDivergence H dH y x = (dH x - dH y) (q - y) := by
  simp only [bregmanDivergence, map_sub, ContinuousLinearMap.sub_apply]
  ring

/-- A convex function lies above its genuine derivative supporting plane. -/
theorem convex_supporting_within_derivative {S : Set E} {H : E → ℝ}
    {x q : E} {H' : E →L[ℝ] ℝ} (hH : ConvexOn ℝ S H)
    (hx : x ∈ S) (hq : q ∈ S) (hd : HasFDerivWithinAt H H' S x) :
    H' (q - x) ≤ H q - H x := by
  have hmaps : MapsTo (AffineMap.lineMap x q) (Icc (0 : ℝ) 1) S :=
    hH.1.mapsTo_lineMap hx hq
  have hcurve : ConvexOn ℝ (Icc (0 : ℝ) 1) (H ∘ AffineMap.lineMap x q) :=
    (hH.comp_affineMap (AffineMap.lineMap x q)).subset hmaps (convex_Icc 0 1)
  have hder : HasDerivWithinAt (H ∘ AffineMap.lineMap x q) (H' (q - x))
      (Icc (0 : ℝ) 1) 0 :=
    hd.comp_hasDerivWithinAt_of_eq 0 AffineMap.hasDerivWithinAt_lineMap hmaps (by simp)
  have h := hcurve.le_slope_of_hasDerivWithinAt (x := 0) (y := 1)
    (by norm_num) (by norm_num) (by norm_num) hder
  simpa [slope_def_field, Function.comp_def] using h

theorem bregmanDivergence_nonneg {S : Set E} {H : E → ℝ}
    {dH : E → E →L[ℝ] ℝ} {x q : E} (hH : ConvexOn ℝ S H)
    (hx : x ∈ S) (hq : q ∈ S) (hd : HasFDerivWithinAt H (dH x) S x) :
    0 ≤ bregmanDivergence H dH q x := by
  have h := convex_supporting_within_derivative hH hx hq hd
  unfold bregmanDivergence
  linarith

/-- Actual constrained minimization implies the relevant first-order inequality. -/
theorem constrained_minimum_first_order {S : Set E} {f : E → ℝ}
    {y q : E} {f' : E →L[ℝ] ℝ} (hS : Convex ℝ S) (hy : y ∈ S) (hq : q ∈ S)
    (hmin : IsMinOn f S y) (hd : HasFDerivWithinAt f f' S y) :
    0 ≤ f' (q - y) :=
  hmin.localize.hasFDerivWithinAt_nonneg hd
    (sub_mem_posTangentConeAt_of_segment_subset (hS.segment_subset hy hq))

theorem mirror_objective_derivative {S : Set E} {H : E → ℝ}
    {dH : E → E →L[ℝ] ℝ} {x y : E} (L : E →L[ℝ] ℝ)
    (hd : HasFDerivWithinAt H (dH y) S y) :
    HasFDerivWithinAt (fun z => L z + bregmanDivergence H dH z x)
      (L + dH y - dH x) S y := by
  have hbase := (((L.hasFDerivAt.hasFDerivWithinAt.add hd).sub_const (H x)).sub
    (dH x).hasFDerivAt.hasFDerivWithinAt).add_const (dH x x)
  convert hbase using 1
  funext z
  simp only [bregmanDivergence, map_sub]
  ring

/-- The Bregman update inequality is proved from the minimization rule. -/
theorem mirror_update_inequality {S : Set E} {H : E → ℝ}
    {dH : E → E →L[ℝ] ℝ} {x y q : E} (L : E →L[ℝ] ℝ)
    (hS : Convex ℝ S) (hy : y ∈ S) (hq : q ∈ S)
    (hd : HasFDerivWithinAt H (dH y) S y)
    (hmin : IsMinOn (fun z => L z + bregmanDivergence H dH z x) S y) :
    bregmanDivergence H dH q y ≤ bregmanDivergence H dH q x +
      L q + mirrorStability H dH L x y := by
  have hfirst := constrained_minimum_first_order hS hy hq hmin
    (mirror_objective_derivative L hd)
  have hid := bregman_three_point_identity H dH q x y
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply, map_sub] at hfirst hid
  unfold mirrorStability
  linarith

/-- The full finite telescope, retaining the terminal divergence. -/
theorem mirror_descent_telescope {S : Set E} {H : E → ℝ}
    {dH : E → E →L[ℝ] ℝ} {x : ℕ → E} {L : ℕ → E →L[ℝ] ℝ} {q : E}
    (hS : Convex ℝ S) (hx : ∀ t, x t ∈ S) (hq : q ∈ S)
    (hd : ∀ t, HasFDerivWithinAt H (dH (x (t + 1))) S (x (t + 1)))
    (hmin : ∀ t, IsMinOn
      (fun z => L t z + bregmanDivergence H dH z (x t)) S (x (t + 1))) (n : ℕ) :
    bregmanDivergence H dH q (x n) ≤ bregmanDivergence H dH q (x 0) +
      ∑ t ∈ Finset.range n, (L t q + mirrorStability H dH (L t) (x t) (x (t + 1))) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep := mirror_update_inequality (L n) hS (hx (n + 1)) hq (hd n) (hmin n)
    rw [Finset.sum_range_succ]
    linarith

/-- Dropping a proved nonnegative terminal divergence gives the online regret bound. -/
theorem mirror_descent_regret {S : Set E} {H : E → ℝ}
    {dH : E → E →L[ℝ] ℝ} {x : ℕ → E} {L : ℕ → E →L[ℝ] ℝ} {q : E}
    (hH : ConvexOn ℝ S H) (hx : ∀ t, x t ∈ S) (hq : q ∈ S)
    (hd : ∀ z ∈ S, HasFDerivWithinAt H (dH z) S z)
    (hmin : ∀ t, IsMinOn
      (fun z => L t z + bregmanDivergence H dH z (x t)) S (x (t + 1))) (n : ℕ) :
    -(∑ t ∈ Finset.range n, L t q) ≤ bregmanDivergence H dH q (x 0) +
      ∑ t ∈ Finset.range n, mirrorStability H dH (L t) (x t) (x (t + 1)) := by
  have htel := mirror_descent_telescope hH.1 hx hq (fun t => hd _ (hx (t + 1))) hmin n
  have hnonneg := bregmanDivergence_nonneg hH (hx n) hq (hd _ (hx n))
  rw [Finset.sum_add_distrib] at htel
  linarith

/-- A separately proved upper bound for each realized stability cost may be substituted. -/
theorem mirror_descent_regret_of_stability_bound {S : Set E} {H : E → ℝ}
    {dH : E → E →L[ℝ] ℝ} {x : ℕ → E} {L : ℕ → E →L[ℝ] ℝ} {q : E} {V : ℕ → ℝ}
    (hH : ConvexOn ℝ S H) (hx : ∀ t, x t ∈ S) (hq : q ∈ S)
    (hd : ∀ z ∈ S, HasFDerivWithinAt H (dH z) S z)
    (hmin : ∀ t, IsMinOn
      (fun z => L t z + bregmanDivergence H dH z (x t)) S (x (t + 1)))
    (hV : ∀ t, mirrorStability H dH (L t) (x t) (x (t + 1)) ≤ V t) (n : ℕ) :
    -(∑ t ∈ Finset.range n, L t q) ≤ bregmanDivergence H dH q (x 0) +
      ∑ t ∈ Finset.range n, V t := by
  exact (mirror_descent_regret hH hx hq hd hmin n).trans
    (add_le_add_left (Finset.sum_le_sum (fun t _ => hV t)) _)

end HeavyTail
