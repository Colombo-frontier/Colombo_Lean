import Problem254
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
open scoped BigOperators
namespace Paper254

/-- The admissible class is nonvacuous: constant losses have the stipulated
within-domain gradients and are exp-concave for every eta. -/
theorem constant_loss_admissible {d : ℕ} {D G η : ℝ}
    (W : Domain d D) (hG : 0 ≤ G) (c : ℝ) :
    AdmissibleLoss W G η (fun _ => c) := by
  constructor
  · exact concaveOn_const _ W.convex
  · intro w _
    exact ⟨0, hasGradientWithinAt_const (c := c) (s := W.carrier) (x := w),
      by simpa using hG⟩

theorem admissible_lipschitz {d : ℕ} {D G η : ℝ} {W : Domain d D}
    {f : Loss d} (hf : AdmissibleLoss W G η f)
    (x y : W.carrier) : ‖f y.val - f x.val‖ ≤ G * ‖y.val - x.val‖ := by
  classical
  let grad : Space d → Space d := fun z =>
    if hz : z ∈ W.carrier then (hf.gradient z hz).choose else 0
  have hgrad : ∀ z ∈ W.carrier,
      HasGradientWithinAt f (grad z) W.carrier z ∧ ‖grad z‖ ≤ G := by
    intro z hz
    simpa only [grad, dif_pos hz] using (hf.gradient z hz).choose_spec
  let deriv : Space d → Space d →L[ℝ] ℝ :=
    fun z => InnerProductSpace.toDual ℝ (Space d) (grad z)
  have hd : ∀ z ∈ W.carrier, HasFDerivWithinAt f (deriv z) W.carrier z := by
    intro z hz
    exact (hgrad z hz).1.hasFDerivWithinAt
  have hb : ∀ z ∈ W.carrier, ‖deriv z‖ ≤ G := by
    intro z hz
    simpa [deriv] using (hgrad z hz).2
  exact W.convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hd hb x.property y.property

/-- A proved branch of the main frontier, derived from the actual loss
assumptions, not from an assumed regret inequality. -/
theorem linear_regret_bound {d T : ℕ} {D G η : ℝ} {W : Domain d D}
    (A : OnlineLearner W T) (f : Fin T → Loss d) (u : Fin T → W.carrier)
    (hG : 0 ≤ G) (hf : ∀ t, AdmissibleLoss W G η (f t)) :
    regret A f u ≤ G * D * T := by
  have hpoint : ∀ t, f t (predictions A f t).val - f t (u t).val ≤ G * D := by
    intro t
    have hl := admissible_lipschitz (hf t) (u t) (predictions A f t)
    have hd := W.diameter _ (predictions A f t).property _ (u t).property
    calc
      f t (predictions A f t).val - f t (u t).val
          ≤ ‖f t (predictions A f t).val - f t (u t).val‖ := Real.le_norm_self _
      _ ≤ G * ‖(predictions A f t).val - (u t).val‖ := hl
      _ ≤ G * D := mul_le_mul_of_nonneg_left hd hG
  calc
    regret A f u ≤ ∑ _t : Fin T, G * D := Finset.sum_le_sum (fun t _ => hpoint t)
    _ = G * D * T := by simp [mul_comm]

theorem constant_learner_exists {d T : ℕ} {D : ℝ} (W : Domain d D) :
    Nonempty (OnlineLearner W T) := by
  obtain ⟨w, hw⟩ := W.nonempty
  exact ⟨fun _ _ => ⟨w, hw⟩⟩

end Paper254
#print axioms Paper254.constant_loss_admissible
#print axioms Paper254.admissible_lipschitz
#print axioms Paper254.linear_regret_bound
