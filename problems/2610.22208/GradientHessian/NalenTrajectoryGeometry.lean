import GradientHessian.NalenTaylor

/-! Geometry of the literal NALEN positions and snapshot schedule. The
distance estimates use only its actual updates and the trust-region radius. -/

noncomputable section
namespace GradientHessian.Nalen
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def midpoint (x δ : E) : E := x+(1/2 : ℝ) • δ

theorem midpoint_sub (x δ δ' : E) :
    midpoint x δ-midpoint x δ'=(1/2 : ℝ) • (δ-δ') := by
  simp only [midpoint,smul_sub]
  abel

theorem norm_midpoint_sub (x y δ δ' : E) :
    ‖midpoint x δ-midpoint y δ'‖ ≤ ‖x-y‖+(1/2 : ℝ)*‖δ-δ'‖ := by
  have he : midpoint x δ-midpoint y δ'=(x-y)+(1/2 : ℝ) • (δ-δ') := by
    simp only [midpoint,smul_sub]
    abel
  rw [he]
  simpa only [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0 : ℝ)<1/2)] using
    norm_add_le (x-y) ((1/2 : ℝ) • (δ-δ'))

omit [NormedSpace ℝ E] in
theorem trajectory_displacement {D : ℝ} (x δ : ℕ → E)
    (hx : ∀ n,x (n+1)=x n+δ (n+1)) (hδ : ∀ n,‖δ n‖ ≤ D) (p r : ℕ) :
    ‖x (p+r)-x p‖ ≤ (r : ℝ)*D := by
  induction r with
  | zero => simp
  | succ r ih =>
    calc
      ‖x (p+(r+1))-x p‖ ≤ ‖x (p+r+1)-x (p+r)‖+‖x (p+r)-x p‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ = ‖δ (p+r+1)‖+‖x (p+r)-x p‖ := by rw [hx]; simp
      _ ≤ D+(r : ℝ)*D := add_le_add (hδ _) ih
      _ = ((r+1 : ℕ) : ℝ)*D := by push_cast; ring

def snapshotIndex (m n : ℕ) : ℕ := n-n%m

theorem snapshot_distance {D : ℝ} (hD : 0 ≤ D) (m : ℕ) (hm : 1 ≤ m)
    (x δ : ℕ → E) (hx : ∀ n,x (n+1)=x n+δ (n+1)) (hδ : ∀ n,‖δ n‖ ≤ D) (n : ℕ) :
    ‖midpoint (x (snapshotIndex m n)) (δ (snapshotIndex m n))-midpoint (x n) (δ n)‖ ≤ (m : ℝ)*D := by
  have hp : snapshotIndex m n+n%m=n := Nat.sub_add_cancel (Nat.mod_le n m)
  have hd := trajectory_displacement x δ hx hδ (snapshotIndex m n) (n%m)
  rw [hp,norm_sub_rev] at hd
  have he : ‖δ (snapshotIndex m n)-δ n‖ ≤ 2*D :=
    (norm_sub_le _ _).trans (by linarith [hδ (snapshotIndex m n),hδ n])
  have hh := norm_midpoint_sub (x (snapshotIndex m n)) (x n)
    (δ (snapshotIndex m n)) (δ n)
  have hn : ((n%m : ℕ) : ℝ)+1 ≤ (m : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.mod_lt n (by omega))
  have hb := mul_le_mul_of_nonneg_right hn hD
  nlinarith only [hd,he,hh,hb]

theorem prediction_displacement {D : ℝ} (x δ δ' : E) (hδ : ‖δ‖ ≤ D) (hδ' : ‖δ'‖ ≤ D) :
    ‖midpoint x δ-midpoint x δ'‖=(1/2 : ℝ)*‖δ-δ'‖ ∧
      ‖midpoint x δ-midpoint x δ'‖ ≤ D := by
  have he : ‖midpoint x δ-midpoint x δ'‖=(1/2 : ℝ)*‖δ-δ'‖ := by
    rw [midpoint_sub,norm_smul]
    norm_num
  refine ⟨he,?_⟩
  rw [he]
  have h := (norm_sub_le δ δ').trans (add_le_add hδ hδ')
  linarith

end GradientHessian.Nalen
