import SecondOrder.CappedHiddenIndependence
import SecondOrder.FirstOrderStageContinuation

open scoped Classical

namespace SecondOrder
noncomputable section
variable {d T : ℕ}

def firstOrderLiftedIndex {R : ℝ}
    (index : ∀ n, FiniteHistory Unit (FirstOrderCoefficients d T R) n → ℕ)
    (n : ℕ) (h : FiniteHistory ((Fin d → Bool) × Unit) (FirstOrderCoefficients d T R) n) : ℕ :=
  index n (finiteHistoryMapInitial Prod.snd n h)

theorem firstOrderPrefixCoefficientLaw_update_past (Θ : Fin (T+1) → (Fin d → Bool))
    (i : Fin (T+1)) (θ : (Fin d → Bool)) (R : ℝ) (hR : 2≤R)
    (k : ℕ) (hk : k ≤ i.val) :
    firstOrderPrefixCoefficientLaw (Function.update Θ i θ) R hR k=firstOrderPrefixCoefficientLaw Θ R hR k := by
  apply firstOrderPrefixCoefficientLaw_hidden_invariant
  intro j hj
  have hne : j≠i := by intro he; subst j; omega
  simp only [Function.update_of_ne hne]

def firstOrderFixedReference (Θ : Fin (T+1) → (Fin d → Bool)) (R : ℝ) (hR : 2≤R)
    (index : ∀ n, FiniteHistory Unit (FirstOrderCoefficients d T R) n → ℕ) (stage : ℕ)
    (n : ℕ) (h : FiniteHistory Unit (FirstOrderCoefficients d T R) n) : PMF (FirstOrderCoefficients d T R) :=
  firstOrderPrefixCoefficientLaw Θ R hR (if index n h=stage then stage else index n h+1)

/-- The capped reference transition of a fixed stage does not read its hidden
vector. The response index is computed from the hidden-erased history. -/
theorem firstOrderCappedReference_hidden (Θ : Fin (T+1) → (Fin d → Bool))
    (R : ℝ) (hR : 2≤R) (i : Fin (T+1))
    (index : ∀ n, FiniteHistory Unit (FirstOrderCoefficients d T R) n → ℕ)
    (hindex : ∀ n h, index n h ≤ i.val) (cap : ℕ) :
    cappedTransition (firstOrderStageSelected (firstOrderLiftedIndex index) i.val) cap
      (firstOrderStageReference (fun s : (Fin d → Bool) × Unit => Function.update Θ i s.1) R hR (firstOrderLiftedIndex index) i.val)
      (firstOrderStageDummy (fun s : (Fin d → Bool) × Unit => Function.update Θ i s.1) R hR)=
    hiddenIndependentTransition
      (cappedTransition (firstOrderStageSelected index i.val) cap (firstOrderFixedReference Θ R hR index i.val)
        (fun _ _ => firstOrderPrefixCoefficientLaw Θ R hR 0)) := by
  have hL : firstOrderStageReference (fun s : (Fin d → Bool) × Unit => Function.update Θ i s.1) R hR
      (firstOrderLiftedIndex index) i.val=hiddenIndependentTransition (firstOrderFixedReference Θ R hR index i.val) := by
    funext n h
    apply firstOrderPrefixCoefficientLaw_update_past
    have hi := hindex n (finiteHistoryMapInitial Prod.snd n h)
    change (if index n (finiteHistoryMapInitial Prod.snd n h)=i.val then i.val
      else index n (finiteHistoryMapInitial Prod.snd n h)+1) ≤ i.val
    split_ifs <;> omega
  have hD : firstOrderStageDummy (fun s : (Fin d → Bool) × Unit => Function.update Θ i s.1) R hR=
      hiddenIndependentTransition (fun _ _ => firstOrderPrefixCoefficientLaw Θ R hR 0) := by
    funext n h
    exact firstOrderPrefixCoefficientLaw_update_past Θ i _ R hR 0 (Nat.zero_le _)
  rw [hL, hD]
  exact cappedTransition_hidden (firstOrderStageSelected index i.val) cap _ _

end
end SecondOrder
