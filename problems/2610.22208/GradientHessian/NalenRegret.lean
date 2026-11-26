import GradientHessian.NalenExtragradient

/-! Telescoping the actual extragradient one-step inequalities. This
retains the movement penalties and obtains a bound independent of the
number of steps in an averaging block. -/

noncomputable section
namespace GradientHessian.Nalen
open scoped InnerProductSpace BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
theorem norm_sub_sq_le_two (x y z : E) :
    ‖x-y‖^2 ≤ 2*‖x-z‖^2+2*‖y-z‖^2 := by
  have h := norm_sub_le_norm_sub_add_norm_sub x z y
  rw [norm_sub_rev z y] at h
  nlinarith [norm_nonneg (x-y),norm_nonneg (x-z),norm_nonneg (y-z),
    sq_nonneg (‖x-z‖-‖y-z‖)]

theorem extragradient_potential {η C : ℝ} (hη : 0 < η) (hC : 0 ≤ C)
    (hstep : 8*η^2*C^2 ≤ 1) (g h δ δprev v w u : E)
    (hh : 0 ≤ ⟪η • h+δ-v,w-δ⟫_ℝ)
    (hg : 0 ≤ ⟪η • g+w-v,u-w⟫_ℝ)
    (herr : ‖h-g‖ ≤ C*‖δ-δprev‖) :
    ⟪g,δ-u⟫_ℝ ≤
      (‖u-v‖^2/(2*η)+2*η*C^2*‖δprev-v‖^2)-
      (‖u-w‖^2/(2*η)+2*η*C^2*‖δ-w‖^2) := by
  have he := extragradient_step hη g h δ v w u hh hg
  have he2 := (sq_le_sq₀ (norm_nonneg (h-g)) (mul_nonneg hC (norm_nonneg _))).2 herr
  have hd := mul_le_mul_of_nonneg_left (norm_sub_sq_le_two δ δprev v) (sq_nonneg C)
  have herr2 : ‖h-g‖^2 ≤ 2*C^2*(‖δ-v‖^2+‖δprev-v‖^2) := by
    rw [mul_pow] at he2
    nlinarith only [he2,hd]
  have herr3 := mul_le_mul_of_nonneg_left herr2 hη.le
  have hc4 : 2*η*C^2 ≤ 1/(4*η) := by
    apply (le_div_iff₀ (show 0 < 4*η by positivity)).2
    nlinarith only [hstep]
  have hc2 : 2*η*C^2 ≤ 1/(2*η) := by
    apply (le_div_iff₀ (show 0 < 2*η by positivity)).2
    nlinarith only [hstep]
  have hb := mul_le_mul_of_nonneg_right hc2 (sq_nonneg ‖δ-v‖)
  have ha := mul_le_mul_of_nonneg_right hc4 (sq_nonneg ‖δ-w‖)
  simp only [div_eq_mul_inv,one_mul] at he hb ha ⊢
  nlinarith only [he,herr3,hb,ha]

theorem extragradient_block_regret {η C D : ℝ} (hη : 0 < η) (hC : 0 ≤ C)
    (hstep : 8*η^2*C^2 ≤ 1) (q : ℕ) (g h δ v : ℕ → E) (u : E)
    (hu : ‖u‖ ≤ D) (hδ : ∀ n, ‖δ n‖ ≤ D) (hv : ∀ n, ‖v n‖ ≤ D)
    (hh : ∀ n < q,0 ≤ ⟪η • h n+δ (n+1)-v n,v (n+1)-δ (n+1)⟫_ℝ)
    (hg : ∀ n < q,0 ≤ ⟪η • g n+v (n+1)-v n,u-v (n+1)⟫_ℝ)
    (herr : ∀ n < q,‖h n-g n‖ ≤ C*‖δ (n+1)-δ n‖) :
    ∑ n ∈ Finset.range q,⟪g n,δ (n+1)-u⟫_ℝ ≤ 3*D^2/η := by
  let P (n : ℕ) := ‖u-v n‖^2/(2*η)+2*η*C^2*‖δ n-v n‖^2
  have hsum (r : ℕ) (hr : r ≤ q) :
      ∑ n ∈ Finset.range r,⟪g n,δ (n+1)-u⟫_ℝ ≤ P 0-P r := by
    induction r with
    | zero => simp
    | succ r ih =>
      rw [Finset.sum_range_succ]
      have hn : r < q := by omega
      have hi := ih (by omega)
      have hs := extragradient_potential hη hC hstep (g r) (h r)
        (δ (r+1)) (δ r) (v r) (v (r+1)) u (hh r hn) (hg r hn) (herr r hn)
      change _ ≤ P r-P (r+1) at hs
      linarith
  have hp : 0 ≤ P q := by dsimp [P]; positivity
  have hD : 0 ≤ D := (norm_nonneg u).trans hu
  have hdiff (x y : E) (hx : ‖x‖ ≤ D) (hy : ‖y‖ ≤ D) : ‖x-y‖^2 ≤ 4*D^2 := by
    have hnorm := (norm_sub_le x y).trans (add_le_add hx hy)
    nlinarith [norm_nonneg (x-y)]
  have hu0 := hdiff u (v 0) hu (hv 0)
  have hd0 := hdiff (δ 0) (v 0) (hδ 0) (hv 0)
  have hc : 2*η*C^2 ≤ 1/(4*η) := by
    apply (le_div_iff₀ (show 0 < 4*η by positivity)).2
    nlinarith only [hstep]
  have ha := div_le_div_of_nonneg_right hu0 (show 0 ≤ 2*η by positivity)
  have hb := mul_le_mul_of_nonneg_left hd0 (show 0 ≤ 2*η*C^2 by positivity)
  have hc' := mul_le_mul_of_nonneg_right hc (show 0 ≤ 4*D^2 by positivity)
  have htotal := hsum q le_rfl
  dsimp [P] at htotal hp
  have he : 4*D^2/(2*η)+(1/(4*η))*(4*D^2)=3*D^2/η := by ring
  rw [← he]
  linarith only [htotal,hp,ha,hb,hc']

end GradientHessian.Nalen
