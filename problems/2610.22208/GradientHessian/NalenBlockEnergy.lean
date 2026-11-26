import GradientHessian.NalenMidpoint
import GradientHessian.NalenTrajectory

/-! The actual objective increments telescope across every complete
averaging block. The cubic midpoint error is uniform without a Hessian
norm bound. -/

noncomputable section
namespace GradientHessian.Nalen
open scoped InnerProductSpace BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem ValidSteps.step_energy {f : E → ℝ} {D η : ℝ} {N : ℕ} {s : Iterates E}
    (hs : ValidSteps f D η N s) (hf : ContDiff ℝ 2 f)
    (hL : LipschitzWith 1 (fderiv ℝ (fderiv ℝ f))) (n : ℕ) (hn : n < N) :
    f (s.x (n+1))-f (s.x n) ≤
      ⟪gradient f (s.queryPoint n),s.δ (n+1)⟫_ℝ+D^3/4 := by
  have ht := midpoint_descent_error hf hL (s.x n) (s.δ (n+1))
  rw [← hs.x_step n hn] at ht
  change ‖f (s.x (n+1))-f (s.x n)-⟪gradient f (s.queryPoint n),s.δ (n+1)⟫_ℝ‖ ≤ _ at ht
  simp only [NNReal.coe_one,Real.norm_eq_abs] at ht
  have hpow : ‖s.δ (n+1)‖^3 ≤ D^3 := by
    exact pow_le_pow_left₀ (norm_nonneg _) (hs.delta_norm _ (by omega)) 3
  have he : (1 : ℝ)/4*‖s.δ (n+1)‖^3 ≤ D^3/4 := by linarith
  have hu := (abs_le.mp (ht.trans he)).2
  linarith

theorem ValidSteps.block_energy {f : E → ℝ} {D η : ℝ} {N : ℕ} {s : Iterates E}
    (hs : ValidSteps f D η N s) (hf : ContDiff ℝ 2 f)
    (hL : LipschitzWith 1 (fderiv ℝ (fderiv ℝ f)))
    (p q : ℕ) (hpq : p+q ≤ N) :
    f (s.x (p+q))-f (s.x p) ≤
      (∑ j ∈ Finset.range q,⟪gradient f (s.queryPoint (p+j)),s.δ (p+j+1)⟫_ℝ)+
        (q : ℝ)*D^3/4 := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hprev := ih (by omega)
    have hnext := hs.step_energy hf hL (p+q) (by omega)
    rw [Finset.sum_range_succ]
    simp only [Nat.cast_add,Nat.cast_one,Nat.add_assoc] at hprev hnext ⊢
    linarith

end GradientHessian.Nalen
