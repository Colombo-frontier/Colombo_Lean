import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Order.OrderClosed

/-! Differentiable gluing on the real line, including the join itself.
Equal endpoint values and derivatives are proved by each concrete user. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open Set Filter Topology

def scalarJoin (a : ℝ) (f g : ℝ → ℝ) (x : ℝ) : ℝ := if x ≤ a then f x else g x

theorem scalarJoin_continuous (a : ℝ) (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (he : f a = g a) : Continuous (scalarJoin a f g) := by
  apply Continuous.if_le hf hg continuous_id continuous_const
  intro x hx
  change x = a at hx
  simpa only [hx] using he

theorem scalarJoin_hasDerivAt (a : ℝ) (f g f' g' : ℝ → ℝ)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hg : ∀ x, HasDerivAt g (g' x) x)
    (he : f a = g a) (he' : f' a = g' a) (x : ℝ) :
    HasDerivAt (scalarJoin a f g) (scalarJoin a f' g' x) x := by
  rcases lt_trichotomy x a with hx | hx | hx
  · rw [scalarJoin, if_pos hx.le]
    apply (hf x).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hx] with y hy
    simp only [scalarJoin, if_pos hy.le]
  · subst x
    rw [scalarJoin, if_pos le_rfl]
    have hl : HasDerivWithinAt (scalarJoin a f g) (f' a) (Iic a) a :=
      (hf a).hasDerivWithinAt.congr_of_mem
        (fun y hy => by simp only [scalarJoin, if_pos (show y ≤ a from hy)]) (by simp)
    have hr : HasDerivWithinAt (scalarJoin a f g) (f' a) (Ici a) a := by
      apply ((hg a).congr_deriv he'.symm).hasDerivWithinAt.congr_of_mem _ (show a ∈ Ici a by simp)
      intro y hy
      by_cases hya : y ≤ a
      · have hy' : y = a := le_antisymm hya hy
        subst y
        simp only [scalarJoin, if_pos le_rfl, he]
      · simp only [scalarJoin, if_neg hya]
    simpa only [Iic_union_Ici, hasDerivWithinAt_univ] using hl.union hr
  · rw [scalarJoin, if_neg (not_le.mpr hx)]
    apply (hg x).congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hx] with y hy
    simp only [scalarJoin, if_neg (not_le.mpr hy)]

end FreshGradientMinimax
