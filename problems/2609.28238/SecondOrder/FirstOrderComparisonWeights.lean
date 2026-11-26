import SecondOrder.FirstOrderComparisonPrefixDependence

open scoped Classical ENNReal

namespace SecondOrder
noncomputable section
variable {d T : ℕ} {S : Type*}

theorem firstOrderComparisonRun_tape_congr (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β : ℝ) {R : ℝ}
    (z z' : ℕ → FirstOrderCoefficients d T R) :
    ∀ n, (∀ t, t<n → z t=z' t) → firstOrderComparisonRun P Θ A β z n=firstOrderComparisonRun P Θ A β z' n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hz
    change firstOrderComparisonStep P Θ A β n (firstOrderComparisonRun P Θ A β z n) (z n)=
      firstOrderComparisonStep P Θ A β n (firstOrderComparisonRun P Θ A β z' n) (z' n)
    rw [ih (fun t ht => hz t (by omega)), hz n (by omega)]

theorem firstOrderComparisonIndex_tape_congr (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β : ℝ) {R : ℝ}
    (z z' : ℕ → FirstOrderCoefficients d T R) (n : ℕ) (hz : ∀ t, t<n → z t=z' t) :
    firstOrderComparisonIndex P Θ A β z n=firstOrderComparisonIndex P Θ A β z' n := by
  unfold firstOrderComparisonIndex firstOrderComparisonQuery
  rw [firstOrderComparisonRun_tape_congr P Θ A β z z' n hz]

/-- Likelihood of a coefficient tape under the actual adaptive prefix laws. -/
def firstOrderComparisonWeight (P : FirstOrderPolicy d T S) (Θ : Fin (T+1) → (Fin d → Bool))
    (A β R : ℝ) (hR : 2≤R) (z : ℕ → FirstOrderCoefficients d T R) : ℕ → ℝ≥0∞
  | 0 => 1
  | n+1 => firstOrderComparisonWeight P Θ A β R hR z n*
      firstOrderPrefixCoefficientLaw Θ R hR (firstOrderComparisonIndex P Θ A β z n+1) (z n)

theorem firstOrderComparisonWeight_ne_zero (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β R : ℝ) (hR : 2≤R)
    (z : ℕ → FirstOrderCoefficients d T R) : ∀ n, firstOrderComparisonWeight P Θ A β R hR z n≠0 := by
  intro n
  induction n with
  | zero => exact one_ne_zero
  | succ n ih => exact mul_ne_zero ih (firstOrderPrefixCoefficientLaw_ne_zero Θ R hR _ _)

theorem firstOrderComparisonWeight_tape_congr (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β R : ℝ) (hR : 2≤R)
    (z z' : ℕ → FirstOrderCoefficients d T R) :
    ∀ n, (∀ t, t<n → z t=z' t) →
      firstOrderComparisonWeight P Θ A β R hR z n=firstOrderComparisonWeight P Θ A β R hR z' n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hz
    simp only [firstOrderComparisonWeight]
    rw [ih (fun t ht => hz t (by omega)),
      firstOrderComparisonIndex_tape_congr P Θ A β z z' n (fun t ht => hz t (by omega)), hz n (by omega)]

/-- The whole tape likelihood, not just the displayed reply, is independent
of hidden blocks beyond the current revealed prefix. -/
theorem firstOrderComparisonWeight_hidden_prefix (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β R : ℝ) (hR : 2≤R)
    (z : ℕ → FirstOrderCoefficients d T R) :
    ∀ n (Θ' : Fin (T+1) → (Fin d → Bool)),
      (∀ i, i.val<(firstOrderComparisonRun P Θ A β z n).1+1 → Θ i=Θ' i) →
      firstOrderComparisonWeight P Θ A β R hR z n=firstOrderComparisonWeight P Θ' A β R hR z n := by
  intro n
  induction n with
  | zero => intro _ _; rfl
  | succ n ih =>
    intro Θ' hΘ
    have hmono : (firstOrderComparisonRun P Θ A β z n).1≤(firstOrderComparisonRun P Θ A β z (n+1)).1 :=
      firstOrderComparisonRun_progress_mono P Θ A β z (Nat.le_succ n)
    have hprev : ∀ i, i.val<(firstOrderComparisonRun P Θ A β z n).1+1 → Θ i=Θ' i :=
      fun i hi => hΘ i (by omega)
    simp only [firstOrderComparisonWeight]
    rw [ih Θ' hprev, firstOrderComparisonLaw_hidden_prefix P Θ Θ' A β R hR z n hΘ]

end
end SecondOrder

