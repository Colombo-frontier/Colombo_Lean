import SecondOrder.ComparisonPrefixDependence

open scoped Classical ENNReal

namespace SecondOrder
noncomputable section
variable {m T : ℕ} {S : Type*}

theorem curvatureComparisonRun_tape_congr (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β : ℝ) {R : ℝ}
    (z z' : ℕ → CurvatureCoefficients m T R) :
    ∀ n, (∀ t, t<n → z t=z' t) → curvatureComparisonRun P Θ A β z n=curvatureComparisonRun P Θ A β z' n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hz
    change curvatureComparisonStep P Θ A β n (curvatureComparisonRun P Θ A β z n) (z n)=
      curvatureComparisonStep P Θ A β n (curvatureComparisonRun P Θ A β z' n) (z' n)
    rw [ih (fun t ht => hz t (by omega)), hz n (by omega)]

theorem curvatureComparisonIndex_tape_congr (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β : ℝ) {R : ℝ}
    (z z' : ℕ → CurvatureCoefficients m T R) (n : ℕ) (hz : ∀ t, t<n → z t=z' t) :
    curvatureComparisonIndex P Θ A β z n=curvatureComparisonIndex P Θ A β z' n := by
  unfold curvatureComparisonIndex curvatureComparisonQuery
  rw [curvatureComparisonRun_tape_congr P Θ A β z z' n hz]

/-- Likelihood of a coefficient tape under the actual adaptive prefix laws. -/
def curvatureComparisonWeight (P : CurvaturePolicy m T S) (Θ : Fin (T+1) → BalancedVector m)
    (A β R : ℝ) (hR : 2≤R) (z : ℕ → CurvatureCoefficients m T R) : ℕ → ℝ≥0∞
  | 0 => 1
  | n+1 => curvatureComparisonWeight P Θ A β R hR z n*
      curvaturePrefixCoefficientLaw Θ R hR (curvatureComparisonIndex P Θ A β z n+1) (z n)

theorem curvatureComparisonWeight_ne_zero (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β R : ℝ) (hR : 2≤R)
    (z : ℕ → CurvatureCoefficients m T R) : ∀ n, curvatureComparisonWeight P Θ A β R hR z n≠0 := by
  intro n
  induction n with
  | zero => exact one_ne_zero
  | succ n ih => exact mul_ne_zero ih (curvaturePrefixCoefficientLaw_ne_zero Θ R hR _ _)

theorem curvatureComparisonWeight_tape_congr (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β R : ℝ) (hR : 2≤R)
    (z z' : ℕ → CurvatureCoefficients m T R) :
    ∀ n, (∀ t, t<n → z t=z' t) →
      curvatureComparisonWeight P Θ A β R hR z n=curvatureComparisonWeight P Θ A β R hR z' n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hz
    simp only [curvatureComparisonWeight]
    rw [ih (fun t ht => hz t (by omega)),
      curvatureComparisonIndex_tape_congr P Θ A β z z' n (fun t ht => hz t (by omega)), hz n (by omega)]

/-- The whole tape likelihood, not just the displayed reply, is independent
of hidden blocks beyond the current revealed prefix. -/
theorem curvatureComparisonWeight_hidden_prefix (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β R : ℝ) (hR : 2≤R)
    (z : ℕ → CurvatureCoefficients m T R) :
    ∀ n (Θ' : Fin (T+1) → BalancedVector m),
      (∀ i, i.val<(curvatureComparisonRun P Θ A β z n).1+1 → Θ i=Θ' i) →
      curvatureComparisonWeight P Θ A β R hR z n=curvatureComparisonWeight P Θ' A β R hR z n := by
  intro n
  induction n with
  | zero => intro _ _; rfl
  | succ n ih =>
    intro Θ' hΘ
    have hmono : (curvatureComparisonRun P Θ A β z n).1≤(curvatureComparisonRun P Θ A β z (n+1)).1 :=
      curvatureComparisonRun_progress_mono P Θ A β z (Nat.le_succ n)
    have hprev : ∀ i, i.val<(curvatureComparisonRun P Θ A β z n).1+1 → Θ i=Θ' i :=
      fun i hi => hΘ i (by omega)
    simp only [curvatureComparisonWeight]
    rw [ih Θ' hprev, curvatureComparisonLaw_hidden_prefix P Θ Θ' A β R hR z n hΘ]

end
end SecondOrder
