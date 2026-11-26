import SecondOrder.CurvatureHorizonConstants

open scoped Classical

namespace SecondOrder
noncomputable section

theorem prefixPositiveFrontier_next_inactive {n : ℕ} (b : Fin n → ℝ) (i : Fin n)
    (hi : ¬0<b i) : prefixPositiveFrontier b (i.val+1)=prefixPositiveFrontier b i.val := by
  unfold prefixPositiveFrontier
  congr 1
  funext j
  by_cases hj : j.val < i.val
  · simp only [hj, show j.val < i.val+1 by omega, true_and]
  · by_cases he : j=i
    · subst j
      simp only [Nat.lt_succ_self, lt_self_iff_false, hi, and_false, if_false]
    · have hne : j.val≠i.val := fun hv => he (Fin.ext hv)
      simp only [hj, show ¬j.val < i.val+1 by omega, false_and, if_false]

variable {m T : ℕ} {S : Type*}

theorem curvatureLimitedProgress_next_inactive (Θ : Fin (T+1) → BalancedVector m)
    (β : ℝ) (x : Point (CurvatureDimension m T)) (i : Fin (T+1))
    (hi : ¬0<periodicCompletion (Θ i) (curvatureDilation m T β x i)) :
    curvatureLimitedProgress Θ β x (i.val+1)=curvatureLimitedProgress Θ β x i.val :=
  prefixPositiveFrontier_next_inactive _ i hi

theorem curvatureLimitedProgress_stage_agree (Θ : Fin (T+1) → BalancedVector m)
    (β : ℝ) (x : Point (CurvatureDimension m T)) (i : Fin (T+1)) (p : ℕ)
    (hp : p+1=i.val ∨ p=i.val)
    (hi : ¬0<periodicCompletion (Θ i) (curvatureDilation m T β x i)) :
    curvatureLimitedProgress Θ β x (p+1)=curvatureLimitedProgress Θ β x i.val := by
  rcases hp with hp | hp
  · rw [hp]
  · rw [hp, curvatureLimitedProgress_next_inactive Θ β x i hi]

/-- Before target activation and before the cap, the continuation returns
exactly the same next policy state as the comparison interaction. -/
theorem curvatureContinuationStep_agree (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β : ℝ) (start n : ℕ) (i : Fin (T+1)) (cap : ℕ)
    (dummy : RichReply (CurvatureDimension m T)) {R : ℝ} (z : CurvatureCoefficients m T R)
    (s : S) (p c : ℕ) (hp : p+1=i.val ∨ p=i.val) (hc : c<cap)
    (hi : ¬0<periodicCompletion (Θ i) (curvatureDilation m T β (P.query (start+n) s) i)) :
    (curvatureComparisonStep P Θ A β (start+n) (p,s) z).2=
      (curvatureContinuationStep P Θ A β start i.val cap dummy n (c,s) z).2 := by
  have hk := curvatureLimitedProgress_stage_agree Θ β (P.query (start+n) s) i p hp hi
  unfold curvatureComparisonStep curvatureContinuationStep
  dsimp only
  rw [if_pos hc, hk]

theorem curvatureComparisonStep_before_target (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β : ℝ) (n : ℕ) (i : Fin (T+1))
    {R : ℝ} (z : CurvatureCoefficients m T R) (s : S) (p : ℕ)
    (hp : p+1=i.val ∨ p=i.val)
    (hi : ¬0<periodicCompletion (Θ i) (curvatureDilation m T β (P.query n s) i)) :
    (curvatureComparisonStep P Θ A β n (p,s) z).1+1=i.val ∨
      (curvatureComparisonStep P Θ A β n (p,s) z).1=i.val := by
  have hk := curvatureLimitedProgress_stage_agree Θ β (P.query n s) i p hp hi
  have hle := (curvatureLimitedProgress_le Θ β (P.query n s) i.val).2
  change max p (curvatureLimitedProgress Θ β (P.query n s) (p+1))+1=i.val ∨
    max p (curvatureLimitedProgress Θ β (P.query n s) (p+1))=i.val
  rw [hk]
  omega

end
end SecondOrder
