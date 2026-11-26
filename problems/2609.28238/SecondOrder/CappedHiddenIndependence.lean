import SecondOrder.CurvatureStageContinuation

open scoped Classical

namespace SecondOrder
noncomputable section

theorem cappedHistoryCount_hidden {H S A : Type} [Fintype H] [Fintype S] [Fintype A]
    (select : ∀ n, FiniteHistory S A n → Bool) (cap : ℕ) :
    ∀ n (h : FiniteHistory (H × S) A n),
    cappedHistoryCount (fun n h => select n (finiteHistoryMapInitial Prod.snd n h)) cap n h=
      cappedHistoryCount select cap n (finiteHistoryMapInitial Prod.snd n h) := by
  intro n
  induction n with
  | zero => intro h; rfl
  | succ n ih =>
    intro h
    simp only [cappedHistoryCount, finiteHistoryMapInitial, ih]

theorem cappedTransition_hidden {H S A : Type} [Fintype H] [Fintype S] [Fintype A]
    (select : ∀ n, FiniteHistory S A n → Bool) (cap : ℕ)
    (K D : ∀ n, FiniteHistory S A n → PMF A) :
    cappedTransition (fun n h => select n (finiteHistoryMapInitial Prod.snd n h)) cap
      (hiddenIndependentTransition (H := H) K) (hiddenIndependentTransition D)=
      hiddenIndependentTransition (cappedTransition select cap K D) := by
  funext n h
  unfold cappedTransition hiddenIndependentTransition
  rw [cappedHistoryCount_hidden]

variable {m T : ℕ}

def curvatureLiftedIndex {R : ℝ}
    (index : ∀ n, FiniteHistory Unit (CurvatureCoefficients m T R) n → ℕ)
    (n : ℕ) (h : FiniteHistory (BalancedVector m × Unit) (CurvatureCoefficients m T R) n) : ℕ :=
  index n (finiteHistoryMapInitial Prod.snd n h)

theorem curvaturePrefixCoefficientLaw_update_past (Θ : Fin (T+1) → BalancedVector m)
    (i : Fin (T+1)) (θ : BalancedVector m) (R : ℝ) (hR : 2≤R)
    (k : ℕ) (hk : k ≤ i.val) :
    curvaturePrefixCoefficientLaw (Function.update Θ i θ) R hR k=curvaturePrefixCoefficientLaw Θ R hR k := by
  apply curvaturePrefixCoefficientLaw_hidden_invariant
  intro j hj
  have hne : j≠i := by intro he; subst j; omega
  simp only [Function.update_of_ne hne]

def curvatureFixedReference (Θ : Fin (T+1) → BalancedVector m) (R : ℝ) (hR : 2≤R)
    (index : ∀ n, FiniteHistory Unit (CurvatureCoefficients m T R) n → ℕ) (stage : ℕ)
    (n : ℕ) (h : FiniteHistory Unit (CurvatureCoefficients m T R) n) : PMF (CurvatureCoefficients m T R) :=
  curvaturePrefixCoefficientLaw Θ R hR (if index n h=stage then stage else index n h+1)

/-- The capped reference transition of a fixed stage does not read its hidden
vector. The response index is computed from the hidden-erased history. -/
theorem curvatureCappedReference_hidden (Θ : Fin (T+1) → BalancedVector m)
    (R : ℝ) (hR : 2≤R) (i : Fin (T+1))
    (index : ∀ n, FiniteHistory Unit (CurvatureCoefficients m T R) n → ℕ)
    (hindex : ∀ n h, index n h ≤ i.val) (cap : ℕ) :
    cappedTransition (curvatureStageSelected (curvatureLiftedIndex index) i.val) cap
      (curvatureStageReference (fun s : BalancedVector m × Unit => Function.update Θ i s.1) R hR (curvatureLiftedIndex index) i.val)
      (curvatureStageDummy (fun s : BalancedVector m × Unit => Function.update Θ i s.1) R hR)=
    hiddenIndependentTransition
      (cappedTransition (curvatureStageSelected index i.val) cap (curvatureFixedReference Θ R hR index i.val)
        (fun _ _ => curvaturePrefixCoefficientLaw Θ R hR 0)) := by
  have hL : curvatureStageReference (fun s : BalancedVector m × Unit => Function.update Θ i s.1) R hR
      (curvatureLiftedIndex index) i.val=hiddenIndependentTransition (curvatureFixedReference Θ R hR index i.val) := by
    funext n h
    apply curvaturePrefixCoefficientLaw_update_past
    have hi := hindex n (finiteHistoryMapInitial Prod.snd n h)
    change (if index n (finiteHistoryMapInitial Prod.snd n h)=i.val then i.val
      else index n (finiteHistoryMapInitial Prod.snd n h)+1) ≤ i.val
    split_ifs <;> omega
  have hD : curvatureStageDummy (fun s : BalancedVector m × Unit => Function.update Θ i s.1) R hR=
      hiddenIndependentTransition (fun _ _ => curvaturePrefixCoefficientLaw Θ R hR 0) := by
    funext n h
    exact curvaturePrefixCoefficientLaw_update_past Θ i _ R hR 0 (Nat.zero_le _)
  rw [hL, hD]
  exact cappedTransition_hidden (curvatureStageSelected index i.val) cap _ _

end
end SecondOrder
