import SecondOrder.FirstOrderComparisonSuccessTransfer
import SecondOrder.FiniteHiddenSlice

open scoped Classical ENNReal

namespace SecondOrder
noncomputable section
variable {d T : ℕ} {S : Type*}

theorem firstOrderUnrevealed_prefix (P : FirstOrderPolicy d T S)
    (Θ Θ' : Fin (T+1) → (Fin d → Bool)) (A β : ℝ) {R : ℝ}
    (z : ℕ → FirstOrderCoefficients d T R) (k n : ℕ)
    (hΘ : ∀ i, i.val<k → Θ i=Θ' i)
    (hu : (firstOrderComparisonRun P Θ A β z n).1+1≤k) :
    (firstOrderComparisonRun P Θ' A β z n).1+1≤k ∧
      firstOrderComparisonRun P Θ A β z n=firstOrderComparisonRun P Θ' A β z n := by
  have he := firstOrderComparisonRun_hidden_prefix P Θ A β z n Θ'
    (fun i hi => hΘ i (by omega))
  exact ⟨he ▸ hu,he⟩

theorem firstOrderUnrevealed_iff_prefix (P : FirstOrderPolicy d T S)
    (Θ Θ' : Fin (T+1) → (Fin d → Bool)) (A β : ℝ) {R : ℝ}
    (z : ℕ → FirstOrderCoefficients d T R) (k n : ℕ)
    (hΘ : ∀ i, i.val<k → Θ i=Θ' i) :
    (firstOrderComparisonRun P Θ A β z n).1+1≤k ↔
      (firstOrderComparisonRun P Θ' A β z n).1+1≤k :=
  ⟨fun hu => (firstOrderUnrevealed_prefix P Θ Θ' A β z k n hΘ hu).1,
    fun hu => (firstOrderUnrevealed_prefix P Θ' Θ A β z k n (fun i hi => (hΘ i hi).symm) hu).1⟩

theorem firstOrderUnrevealed_mass_prefix (P : FirstOrderPolicy d T S)
    (Θ Θ' : Fin (T+1) → (Fin d → Bool)) (A β R : ℝ) (hR : 2≤R)
    (a₀ : FirstOrderCoefficients d T R) (k n : ℕ)
    (h : FiniteHistory Unit (FirstOrderCoefficients d T R) n)
    (hΘ : ∀ i, i.val<k → Θ i=Θ' i)
    (hu : (firstOrderComparisonRun P Θ A β (finiteHistoryTape a₀ n h) n).1+1≤k) :
    firstOrderComparisonSamplingLaw P Θ A β R hR a₀ n h=
      firstOrderComparisonSamplingLaw P Θ' A β R hR a₀ n h := by
  simp only [firstOrderComparisonSamplingLaw_apply]
  exact firstOrderComparisonWeight_hidden_prefix P Θ A β R hR _ n Θ'
    (fun i hi => hΘ i (by omega))

theorem firstOrderHidden_update_prefix (Θ : Fin (T+1) → (Fin d → Bool))
    (i : Fin (T+1)) (θ θ' : (Fin d → Bool)) :
    ∀ j, j.val < i.val → Function.update Θ i θ j=Function.update Θ i θ' j := by
  intro j hj
  have hne : j≠i := by intro he; subst j; exact Nat.lt_irrefl _ hj
  simp only [Function.update_of_ne hne]

end
end SecondOrder

