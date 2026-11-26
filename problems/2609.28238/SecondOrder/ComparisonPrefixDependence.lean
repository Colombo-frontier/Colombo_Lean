import SecondOrder.CurvatureComparison

open scoped Classical

namespace SecondOrder
noncomputable section
variable {m T : ℕ} {S : Type*}

/-- Agreement through the first not-yet-completed block determines the whole
comparison state on the same coefficient tape, including historical progress. -/
theorem curvatureComparisonRun_hidden_prefix (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β : ℝ) {R : ℝ}
    (z : ℕ → CurvatureCoefficients m T R) :
    ∀ n (Θ' : Fin (T+1) → BalancedVector m),
      (∀ i, i.val<(curvatureComparisonRun P Θ A β z n).1+1 → Θ i=Θ' i) →
      curvatureComparisonRun P Θ A β z n=curvatureComparisonRun P Θ' A β z n := by
  intro n
  induction n with
  | zero => intro _ _; rfl
  | succ n ih =>
    intro Θ' hΘ
    have hmono : (curvatureComparisonRun P Θ A β z n).1≤(curvatureComparisonRun P Θ A β z (n+1)).1 :=
      curvatureComparisonRun_progress_mono P Θ A β z (Nat.le_succ n)
    have hprev : ∀ i, i.val<(curvatureComparisonRun P Θ A β z n).1+1 → Θ i=Θ' i :=
      fun i hi => hΘ i (by omega)
    have hs := ih Θ' hprev
    have hk := curvatureLimitedProgress_prefix Θ Θ' β (curvatureComparisonQuery P Θ A β z n)
      ((curvatureComparisonRun P Θ A β z n).1+1) hprev
    have hreply := scaledCurvatureTruncatedReply_hidden_prefix Θ Θ' A β (z n)
      (curvatureComparisonIndex P Θ A β z n) (fun i hi => hΘ i (by
        have hh := curvatureComparisonIndex_le_next P Θ A β z n
        omega)) (curvatureComparisonQuery P Θ A β z n)
    change curvatureComparisonStep P Θ A β n (curvatureComparisonRun P Θ A β z n) (z n)=
      curvatureComparisonStep P Θ' A β n (curvatureComparisonRun P Θ' A β z n) (z n)
    rw [←hs]
    apply Prod.ext
    · exact congrArg (max (curvatureComparisonRun P Θ A β z n).1) hk
    · change P.update n (curvatureComparisonRun P Θ A β z n).2
        (scaledCurvatureTruncatedReply Θ A β (z n) (curvatureComparisonIndex P Θ A β z n)
          (curvatureComparisonQuery P Θ A β z n)) =
        P.update n (curvatureComparisonRun P Θ A β z n).2
        (scaledCurvatureTruncatedReply Θ' A β (z n)
          (curvatureLimitedProgress Θ' β (curvatureComparisonQuery P Θ A β z n)
            ((curvatureComparisonRun P Θ A β z n).1+1)) (curvatureComparisonQuery P Θ A β z n))
      rw [←hk]
      exact congrArg (P.update n (curvatureComparisonRun P Θ A β z n).2) hreply

theorem curvatureComparisonQuery_hidden_prefix (P : CurvaturePolicy m T S)
    (Θ Θ' : Fin (T+1) → BalancedVector m) (A β : ℝ) {R : ℝ}
    (z : ℕ → CurvatureCoefficients m T R) (n : ℕ)
    (hΘ : ∀ i, i.val<(curvatureComparisonRun P Θ A β z n).1+1 → Θ i=Θ' i) :
    curvatureComparisonQuery P Θ A β z n=curvatureComparisonQuery P Θ' A β z n := by
  unfold curvatureComparisonQuery
  rw [curvatureComparisonRun_hidden_prefix P Θ A β z n Θ' hΘ]

theorem curvatureComparisonIndex_hidden_prefix (P : CurvaturePolicy m T S)
    (Θ Θ' : Fin (T+1) → BalancedVector m) (A β : ℝ) {R : ℝ}
    (z : ℕ → CurvatureCoefficients m T R) (n : ℕ)
    (hΘ : ∀ i, i.val<(curvatureComparisonRun P Θ A β z n).1+1 → Θ i=Θ' i) :
    curvatureComparisonIndex P Θ A β z n=curvatureComparisonIndex P Θ' A β z n := by
  have hs := curvatureComparisonRun_hidden_prefix P Θ A β z n Θ' hΘ
  have hx := curvatureComparisonQuery_hidden_prefix P Θ Θ' A β z n hΘ
  unfold curvatureComparisonIndex
  rw [←hs, ←hx]
  exact curvatureLimitedProgress_prefix Θ Θ' β _ _ hΘ

/-- The probability assigned to the next sampled array also depends only on
the hidden prefix exposed by the updated historical progress. -/
theorem curvatureComparisonLaw_hidden_prefix (P : CurvaturePolicy m T S)
    (Θ Θ' : Fin (T+1) → BalancedVector m) (A β R : ℝ) (hR : 2≤R)
    (z : ℕ → CurvatureCoefficients m T R) (n : ℕ)
    (hΘ : ∀ i, i.val<(curvatureComparisonRun P Θ A β z (n+1)).1+1 → Θ i=Θ' i) :
    curvaturePrefixCoefficientLaw Θ R hR (curvatureComparisonIndex P Θ A β z n+1)=
      curvaturePrefixCoefficientLaw Θ' R hR (curvatureComparisonIndex P Θ' A β z n+1) := by
  have hmono : (curvatureComparisonRun P Θ A β z n).1≤(curvatureComparisonRun P Θ A β z (n+1)).1 :=
      curvatureComparisonRun_progress_mono P Θ A β z (Nat.le_succ n)
  have hprev : ∀ i, i.val<(curvatureComparisonRun P Θ A β z n).1+1 → Θ i=Θ' i :=
    fun i hi => hΘ i (by omega)
  rw [←curvatureComparisonIndex_hidden_prefix P Θ Θ' A β z n hprev]
  apply curvaturePrefixCoefficientLaw_hidden_invariant
  intro i hi
  have hh := curvatureComparisonIndex_le_next P Θ A β z n
  exact hΘ i (by omega)

end
end SecondOrder
