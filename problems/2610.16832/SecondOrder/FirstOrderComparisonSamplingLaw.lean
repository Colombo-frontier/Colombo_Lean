import SecondOrder.FirstOrderComparisonStageEntry
import SecondOrder.FiniteHistoryTape

open scoped Classical ENNReal

namespace SecondOrder
noncomputable section
variable {d T : ℕ} {S : Type*}

/-- The actual next-array law of the fair-filled comparison interaction. -/
def firstOrderComparisonTransition (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β R : ℝ) (hR : 2≤R)
    (a₀ : FirstOrderCoefficients d T R) (n : ℕ)
    (h : FiniteHistory Unit (FirstOrderCoefficients d T R) n) :
    PMF (FirstOrderCoefficients d T R) :=
  firstOrderPrefixCoefficientLaw Θ R hR
    (firstOrderComparisonIndex P Θ A β (finiteHistoryTape a₀ n h) n+1)

def firstOrderComparisonSamplingLaw (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β R : ℝ) (hR : 2≤R)
    (a₀ : FirstOrderCoefficients d T R) (n : ℕ) :
    PMF (FiniteHistory Unit (FirstOrderCoefficients d T R) n) :=
  finiteAdaptiveLaw (PMF.pure ()) (firstOrderComparisonTransition P Θ A β R hR a₀) n

/-- The path weights are masses of a normalized probability law. -/
theorem firstOrderComparisonSamplingLaw_apply (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β R : ℝ) (hR : 2≤R)
    (a₀ : FirstOrderCoefficients d T R) :
    ∀ n h, firstOrderComparisonSamplingLaw P Θ A β R hR a₀ n h=
      firstOrderComparisonWeight P Θ A β R hR (finiteHistoryTape a₀ n h) n := by
  intro n
  induction n with
  | zero => intro h; cases h; simp [firstOrderComparisonSamplingLaw, firstOrderComparisonWeight]
  | succ n ih =>
    intro h
    change firstOrderComparisonSamplingLaw P Θ A β R hR a₀ n h.1 *
      firstOrderComparisonTransition P Θ A β R hR a₀ n h.1 h.2 = _
    rw [ih, firstOrderComparisonWeight]
    have ht : ∀ t, t<n → finiteHistoryTape a₀ (n+1) h t=finiteHistoryTape a₀ n h.1 t :=
      finiteHistoryTape_succ_lt a₀ n h
    rw [firstOrderComparisonWeight_tape_congr P Θ A β R hR _ _ n ht,
      firstOrderComparisonIndex_tape_congr P Θ A β _ _ n ht, finiteHistoryTape_succ_at]
    rfl

theorem firstOrderComparisonSamplingLaw_ne_zero (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β R : ℝ) (hR : 2≤R)
    (a₀ : FirstOrderCoefficients d T R) (n : ℕ)
    (h : FiniteHistory Unit (FirstOrderCoefficients d T R) n) :
    firstOrderComparisonSamplingLaw P Θ A β R hR a₀ n h≠0 := by
  rw [firstOrderComparisonSamplingLaw_apply]
  exact firstOrderComparisonWeight_ne_zero P Θ A β R hR _ n

theorem firstOrderComparisonSamplingLaw_default_congr (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β R : ℝ) (hR : 2≤R)
    (a₀ a₁ : FirstOrderCoefficients d T R) (n : ℕ) :
    firstOrderComparisonSamplingLaw P Θ A β R hR a₀ n=
      firstOrderComparisonSamplingLaw P Θ A β R hR a₁ n := by
  ext h
  simp only [firstOrderComparisonSamplingLaw_apply]
  exact firstOrderComparisonWeight_tape_congr P Θ A β R hR _ _ n
    (finiteHistoryTape_default_congr a₀ a₁ n h)

/-- A finite entry history has the same probability after replacing all hidden
blocks at and beyond the new stage. -/
theorem firstOrderStageEntry_mass_prefix (P : FirstOrderPolicy d T S)
    (Θ Θ' : Fin (T+1) → (Fin d → Bool)) (A β R : ℝ) (hR : 2≤R)
    (a₀ : FirstOrderCoefficients d T R) (stage n : ℕ)
    (h : FiniteHistory Unit (FirstOrderCoefficients d T R) n)
    (hΘ : ∀ i, i.val<stage → Θ i=Θ' i) :
    (if firstOrderStageEntry P Θ A β (finiteHistoryTape a₀ n h) stage n
      then firstOrderComparisonSamplingLaw P Θ A β R hR a₀ n h else 0)=
    (if firstOrderStageEntry P Θ' A β (finiteHistoryTape a₀ n h) stage n
      then firstOrderComparisonSamplingLaw P Θ' A β R hR a₀ n h else 0) := by
  simp only [firstOrderComparisonSamplingLaw_apply]
  exact firstOrderStageEntry_weight_prefix P Θ Θ' A β R hR _ stage n hΘ

end
end SecondOrder

