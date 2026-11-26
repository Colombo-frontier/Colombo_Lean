import SecondOrder.CurvatureContinuationAgreement
import SecondOrder.FirstOrderHorizonConstants

open scoped Classical

namespace SecondOrder
noncomputable section
variable {d T : ℕ} {S : Type*}

theorem firstOrderLimitedProgress_next_inactive (Θ : Fin (T+1) → (Fin d → Bool))
    (β : ℝ) (x : Point (FirstOrderDimension d T)) (i : Fin (T+1))
    (hi : ¬0<firstOrderBlockCompletion (Θ i) (firstOrderDilation d T β x i)) :
    firstOrderLimitedProgress Θ β x (i.val+1)=firstOrderLimitedProgress Θ β x i.val :=
  prefixPositiveFrontier_next_inactive _ i hi

theorem firstOrderLimitedProgress_stage_agree (Θ : Fin (T+1) → (Fin d → Bool))
    (β : ℝ) (x : Point (FirstOrderDimension d T)) (i : Fin (T+1)) (p : ℕ)
    (hp : p+1=i.val ∨ p=i.val)
    (hi : ¬0<firstOrderBlockCompletion (Θ i) (firstOrderDilation d T β x i)) :
    firstOrderLimitedProgress Θ β x (p+1)=firstOrderLimitedProgress Θ β x i.val := by
  rcases hp with hp | hp
  · rw [hp]
  · rw [hp, firstOrderLimitedProgress_next_inactive Θ β x i hi]

/-- Before target activation and before the cap, the continuation returns
exactly the same next policy state as the comparison interaction. -/
theorem firstOrderContinuationStep_agree (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β : ℝ) (start n : ℕ) (i : Fin (T+1)) (cap : ℕ)
    (dummy : RichReply (FirstOrderDimension d T)) {R : ℝ} (z : FirstOrderCoefficients d T R)
    (s : S) (p c : ℕ) (hp : p+1=i.val ∨ p=i.val) (hc : c<cap)
    (hi : ¬0<firstOrderBlockCompletion (Θ i) (firstOrderDilation d T β (P.query (start+n) s) i)) :
    (firstOrderComparisonStep P Θ A β (start+n) (p,s) z).2=
      (firstOrderContinuationStep P Θ A β start i.val cap dummy n (c,s) z).2 := by
  have hk := firstOrderLimitedProgress_stage_agree Θ β (P.query (start+n) s) i p hp hi
  unfold firstOrderComparisonStep firstOrderContinuationStep
  dsimp only
  rw [if_pos hc, hk]

theorem firstOrderComparisonStep_before_target (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β : ℝ) (n : ℕ) (i : Fin (T+1))
    {R : ℝ} (z : FirstOrderCoefficients d T R) (s : S) (p : ℕ)
    (hp : p+1=i.val ∨ p=i.val)
    (hi : ¬0<firstOrderBlockCompletion (Θ i) (firstOrderDilation d T β (P.query n s) i)) :
    (firstOrderComparisonStep P Θ A β n (p,s) z).1+1=i.val ∨
      (firstOrderComparisonStep P Θ A β n (p,s) z).1=i.val := by
  have hk := firstOrderLimitedProgress_stage_agree Θ β (P.query n s) i p hp hi
  have hle := (firstOrderLimitedProgress_le Θ β (P.query n s) i.val).2
  change max p (firstOrderLimitedProgress Θ β (P.query n s) (p+1))+1=i.val ∨
    max p (firstOrderLimitedProgress Θ β (P.query n s) (p+1))=i.val
  rw [hk]
  omega

end
end SecondOrder
