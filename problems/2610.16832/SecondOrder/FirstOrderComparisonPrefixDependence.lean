import SecondOrder.FirstOrderComparison

open scoped Classical

namespace SecondOrder
noncomputable section
variable {d T : ℕ} {S : Type*}

/-- Agreement through the first not-yet-completed block determines the whole
comparison state on the same coefficient tape, including historical progress. -/
theorem firstOrderComparisonRun_hidden_prefix (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β : ℝ) {R : ℝ}
    (z : ℕ → FirstOrderCoefficients d T R) :
    ∀ n (Θ' : Fin (T+1) → (Fin d → Bool)),
      (∀ i, i.val<(firstOrderComparisonRun P Θ A β z n).1+1 → Θ i=Θ' i) →
      firstOrderComparisonRun P Θ A β z n=firstOrderComparisonRun P Θ' A β z n := by
  intro n
  induction n with
  | zero => intro _ _; rfl
  | succ n ih =>
    intro Θ' hΘ
    have hmono : (firstOrderComparisonRun P Θ A β z n).1≤(firstOrderComparisonRun P Θ A β z (n+1)).1 :=
      firstOrderComparisonRun_progress_mono P Θ A β z (Nat.le_succ n)
    have hprev : ∀ i, i.val<(firstOrderComparisonRun P Θ A β z n).1+1 → Θ i=Θ' i :=
      fun i hi => hΘ i (by omega)
    have hs := ih Θ' hprev
    have hk := firstOrderLimitedProgress_prefix Θ Θ' β (firstOrderComparisonQuery P Θ A β z n)
      ((firstOrderComparisonRun P Θ A β z n).1+1) hprev
    have hreply := scaledFirstOrderTruncatedReply_hidden_prefix Θ Θ' A β (z n)
      (firstOrderComparisonIndex P Θ A β z n) (fun i hi => hΘ i (by
        have hh := firstOrderComparisonIndex_le_next P Θ A β z n
        omega)) (firstOrderComparisonQuery P Θ A β z n)
    change firstOrderComparisonStep P Θ A β n (firstOrderComparisonRun P Θ A β z n) (z n)=
      firstOrderComparisonStep P Θ' A β n (firstOrderComparisonRun P Θ' A β z n) (z n)
    rw [←hs]
    apply Prod.ext
    · exact congrArg (max (firstOrderComparisonRun P Θ A β z n).1) hk
    · change P.update n (firstOrderComparisonRun P Θ A β z n).2
        (scaledFirstOrderTruncatedReply Θ A β (z n) (firstOrderComparisonIndex P Θ A β z n)
          (firstOrderComparisonQuery P Θ A β z n)) =
        P.update n (firstOrderComparisonRun P Θ A β z n).2
        (scaledFirstOrderTruncatedReply Θ' A β (z n)
          (firstOrderLimitedProgress Θ' β (firstOrderComparisonQuery P Θ A β z n)
            ((firstOrderComparisonRun P Θ A β z n).1+1)) (firstOrderComparisonQuery P Θ A β z n))
      rw [←hk]
      exact congrArg (P.update n (firstOrderComparisonRun P Θ A β z n).2) hreply

theorem firstOrderComparisonQuery_hidden_prefix (P : FirstOrderPolicy d T S)
    (Θ Θ' : Fin (T+1) → (Fin d → Bool)) (A β : ℝ) {R : ℝ}
    (z : ℕ → FirstOrderCoefficients d T R) (n : ℕ)
    (hΘ : ∀ i, i.val<(firstOrderComparisonRun P Θ A β z n).1+1 → Θ i=Θ' i) :
    firstOrderComparisonQuery P Θ A β z n=firstOrderComparisonQuery P Θ' A β z n := by
  unfold firstOrderComparisonQuery
  rw [firstOrderComparisonRun_hidden_prefix P Θ A β z n Θ' hΘ]

theorem firstOrderComparisonIndex_hidden_prefix (P : FirstOrderPolicy d T S)
    (Θ Θ' : Fin (T+1) → (Fin d → Bool)) (A β : ℝ) {R : ℝ}
    (z : ℕ → FirstOrderCoefficients d T R) (n : ℕ)
    (hΘ : ∀ i, i.val<(firstOrderComparisonRun P Θ A β z n).1+1 → Θ i=Θ' i) :
    firstOrderComparisonIndex P Θ A β z n=firstOrderComparisonIndex P Θ' A β z n := by
  have hs := firstOrderComparisonRun_hidden_prefix P Θ A β z n Θ' hΘ
  have hx := firstOrderComparisonQuery_hidden_prefix P Θ Θ' A β z n hΘ
  unfold firstOrderComparisonIndex
  rw [←hs, ←hx]
  exact firstOrderLimitedProgress_prefix Θ Θ' β _ _ hΘ

/-- The probability assigned to the next sampled array also depends only on
the hidden prefix exposed by the updated historical progress. -/
theorem firstOrderComparisonLaw_hidden_prefix (P : FirstOrderPolicy d T S)
    (Θ Θ' : Fin (T+1) → (Fin d → Bool)) (A β R : ℝ) (hR : 2≤R)
    (z : ℕ → FirstOrderCoefficients d T R) (n : ℕ)
    (hΘ : ∀ i, i.val<(firstOrderComparisonRun P Θ A β z (n+1)).1+1 → Θ i=Θ' i) :
    firstOrderPrefixCoefficientLaw Θ R hR (firstOrderComparisonIndex P Θ A β z n+1)=
      firstOrderPrefixCoefficientLaw Θ' R hR (firstOrderComparisonIndex P Θ' A β z n+1) := by
  have hmono : (firstOrderComparisonRun P Θ A β z n).1≤(firstOrderComparisonRun P Θ A β z (n+1)).1 :=
      firstOrderComparisonRun_progress_mono P Θ A β z (Nat.le_succ n)
  have hprev : ∀ i, i.val<(firstOrderComparisonRun P Θ A β z n).1+1 → Θ i=Θ' i :=
    fun i hi => hΘ i (by omega)
  rw [←firstOrderComparisonIndex_hidden_prefix P Θ Θ' A β z n hprev]
  apply firstOrderPrefixCoefficientLaw_hidden_invariant
  intro i hi
  have hh := firstOrderComparisonIndex_le_next P Θ A β z n
  exact hΘ i (by omega)

end
end SecondOrder

