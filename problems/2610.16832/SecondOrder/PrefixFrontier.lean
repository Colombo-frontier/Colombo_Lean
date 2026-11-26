import SecondOrder.SequentialStageCounting

open scoped Classical

namespace SecondOrder
noncomputable section
variable {n : ℕ}

/-- Inspect only the first r blocks when choosing the next response index. -/
def prefixPositiveFrontier (b : Fin n → ℝ) (r : ℕ) : ℕ :=
  Finset.univ.sup (fun i => if i.val<r ∧ 0<b i then i.val+1 else 0)

theorem prefixPositiveFrontier_le_size (b : Fin n → ℝ) (r : ℕ) : prefixPositiveFrontier b r≤n := by
  apply Finset.sup_le
  intro i _
  split_ifs <;> omega

theorem prefixPositiveFrontier_le_cut (b : Fin n → ℝ) (r : ℕ) : prefixPositiveFrontier b r≤r := by
  apply Finset.sup_le
  intro i _
  split_ifs <;> omega

theorem prefixPositiveFrontier_congr (b c : Fin n → ℝ) (r : ℕ)
    (h : ∀ i, i.val<r → b i=c i) : prefixPositiveFrontier b r=prefixPositiveFrontier c r := by
  unfold prefixPositiveFrontier
  congr 1
  funext i
  by_cases hi : i.val<r
  · rw [h i hi]
  · simp only [hi, false_and, if_false]

theorem prefixPositiveFrontier_no_far (b : Fin n → ℝ) (r : ℕ)
    (hfar : ∀ i, r ≤ i.val → ¬0<b i) : prefixPositiveFrontier b r=positiveGateFrontier b := by
  unfold prefixPositiveFrontier positiveGateFrontier
  congr 1
  funext i
  by_cases hi : i.val<r
  · simp only [hi, true_and]
  · simp only [hi, false_and, if_false, if_neg (hfar i (by omega))]

theorem positiveGateFrontier_all_pos (b : Fin n → ℝ) (hb : ∀ i, 0<b i) : positiveGateFrontier b=n := by
  apply le_antisymm (positiveGateFrontier_le b)
  cases n with
  | zero => exact Nat.zero_le _
  | succ n =>
    have hh := Finset.le_sup (f := fun i : Fin (n+1) => if 0<b i then i.val+1 else 0)
      (Finset.mem_univ (Fin.last n))
    simpa only [positiveGateFrontier, hb, if_true, Fin.val_last] using hh

variable {m T : ℕ}

def curvatureLimitedProgress (Θ : Fin (T+1) → BalancedVector m) (β : ℝ)
    (x : Point (CurvatureDimension m T)) (r : ℕ) : ℕ :=
  prefixPositiveFrontier (fun i => periodicCompletion (Θ i) (curvatureDilation m T β x i)) r

theorem curvatureLimitedProgress_le (Θ : Fin (T+1) → BalancedVector m) (β : ℝ)
    (x : Point (CurvatureDimension m T)) (r : ℕ) :
    curvatureLimitedProgress Θ β x r≤T+1 ∧ curvatureLimitedProgress Θ β x r≤r :=
  ⟨prefixPositiveFrontier_le_size _ _, prefixPositiveFrontier_le_cut _ _⟩

theorem curvatureLimitedProgress_prefix (Θ Θ' : Fin (T+1) → BalancedVector m) (β : ℝ)
    (x : Point (CurvatureDimension m T)) (r : ℕ) (hΘ : ∀ i, i.val<r → Θ i=Θ' i) :
    curvatureLimitedProgress Θ β x r=curvatureLimitedProgress Θ' β x r :=
  prefixPositiveFrontier_congr _ _ r (fun i hi => by rw [hΘ i hi])

theorem curvatureLimitedProgress_no_far (Θ : Fin (T+1) → BalancedVector m) (β : ℝ)
    (x : Point (CurvatureDimension m T)) (r : ℕ)
    (hfar : ∀ i, r ≤ i.val → ¬0<periodicCompletion (Θ i) (curvatureDilation m T β x i)) :
    curvatureLimitedProgress Θ β x r=curvatureProgress Θ (curvatureDilation m T β x) :=
  prefixPositiveFrontier_no_far _ r hfar

theorem curvatureLimitedProgress_reply (Θ : Fin (T+1) → BalancedVector m) (A β : ℝ)
    {R : ℝ} (z : CurvatureCoefficients m T R) (x : Point (CurvatureDimension m T)) (r : ℕ)
    (hfar : ∀ i, r ≤ i.val → ¬0<periodicCompletion (Θ i) (curvatureDilation m T β x i)) :
    richReply (scaledCurvatureSample Θ A β) z x =
      scaledCurvatureTruncatedReply Θ A β z (curvatureLimitedProgress Θ β x r) x := by
  rw [curvatureLimitedProgress_no_far Θ β x r hfar]
  exact scaledCurvatureReply_at_progress Θ A β z x

/-- Prefix dependence also covers the terminal index, where every hidden
block has already been revealed. -/
theorem scaledCurvatureTruncatedReply_hidden_prefix (Θ Θ' : Fin (T+1) → BalancedVector m)
    (A β : ℝ) {R : ℝ} (z : CurvatureCoefficients m T R) (k : ℕ)
    (hΘ : ∀ i, i.val<k → Θ i=Θ' i) (x : Point (CurvatureDimension m T)) :
    scaledCurvatureTruncatedReply Θ A β z k x=scaledCurvatureTruncatedReply Θ' A β z k x := by
  by_cases hk : k≤T
  · exact scaledCurvatureTruncatedReply_prefix_invariant Θ Θ' A β z z hk hΘ (fun _ _ => rfl) x
  · have he : Θ=Θ' := funext (fun i => hΘ i (by omega))
    rw [he]

end
end SecondOrder
