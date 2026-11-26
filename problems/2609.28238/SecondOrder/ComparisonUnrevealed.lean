import SecondOrder.FiniteHiddenSlice

open scoped Classical ENNReal

namespace SecondOrder
noncomputable section
variable {m T : ℕ} {S : Type*}

theorem curvatureUnrevealed_prefix (P : CurvaturePolicy m T S)
    (Θ Θ' : Fin (T+1) → BalancedVector m) (A β : ℝ) {R : ℝ}
    (z : ℕ → CurvatureCoefficients m T R) (k n : ℕ)
    (hΘ : ∀ i, i.val<k → Θ i=Θ' i)
    (hu : (curvatureComparisonRun P Θ A β z n).1+1≤k) :
    (curvatureComparisonRun P Θ' A β z n).1+1≤k ∧
      curvatureComparisonRun P Θ A β z n=curvatureComparisonRun P Θ' A β z n := by
  have he := curvatureComparisonRun_hidden_prefix P Θ A β z n Θ'
    (fun i hi => hΘ i (by omega))
  exact ⟨he ▸ hu,he⟩

theorem curvatureUnrevealed_iff_prefix (P : CurvaturePolicy m T S)
    (Θ Θ' : Fin (T+1) → BalancedVector m) (A β : ℝ) {R : ℝ}
    (z : ℕ → CurvatureCoefficients m T R) (k n : ℕ)
    (hΘ : ∀ i, i.val<k → Θ i=Θ' i) :
    (curvatureComparisonRun P Θ A β z n).1+1≤k ↔
      (curvatureComparisonRun P Θ' A β z n).1+1≤k :=
  ⟨fun hu => (curvatureUnrevealed_prefix P Θ Θ' A β z k n hΘ hu).1,
    fun hu => (curvatureUnrevealed_prefix P Θ' Θ A β z k n (fun i hi => (hΘ i hi).symm) hu).1⟩

theorem curvatureUnrevealed_mass_prefix (P : CurvaturePolicy m T S)
    (Θ Θ' : Fin (T+1) → BalancedVector m) (A β R : ℝ) (hR : 2≤R)
    (a₀ : CurvatureCoefficients m T R) (k n : ℕ)
    (h : FiniteHistory Unit (CurvatureCoefficients m T R) n)
    (hΘ : ∀ i, i.val<k → Θ i=Θ' i)
    (hu : (curvatureComparisonRun P Θ A β (finiteHistoryTape a₀ n h) n).1+1≤k) :
    curvatureComparisonSamplingLaw P Θ A β R hR a₀ n h=
      curvatureComparisonSamplingLaw P Θ' A β R hR a₀ n h := by
  simp only [curvatureComparisonSamplingLaw_apply]
  exact curvatureComparisonWeight_hidden_prefix P Θ A β R hR _ n Θ'
    (fun i hi => hΘ i (by omega))

theorem curvatureHidden_update_prefix (Θ : Fin (T+1) → BalancedVector m)
    (i : Fin (T+1)) (θ θ' : BalancedVector m) :
    ∀ j, j.val < i.val → Function.update Θ i θ j=Function.update Θ i θ' j := by
  intro j hj
  have hne : j≠i := by intro he; subst j; exact Nat.lt_irrefl _ hj
  simp only [Function.update_of_ne hne]

end
end SecondOrder
