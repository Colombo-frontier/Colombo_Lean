import SecondOrder.FiniteHistoryTape

open scoped Classical ENNReal

namespace SecondOrder
noncomputable section
variable {m T : ℕ} {S : Type*}

/-- The actual next-array law of the fair-filled comparison interaction. -/
def curvatureComparisonTransition (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β R : ℝ) (hR : 2≤R)
    (a₀ : CurvatureCoefficients m T R) (n : ℕ)
    (h : FiniteHistory Unit (CurvatureCoefficients m T R) n) :
    PMF (CurvatureCoefficients m T R) :=
  curvaturePrefixCoefficientLaw Θ R hR
    (curvatureComparisonIndex P Θ A β (finiteHistoryTape a₀ n h) n+1)

def curvatureComparisonSamplingLaw (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β R : ℝ) (hR : 2≤R)
    (a₀ : CurvatureCoefficients m T R) (n : ℕ) :
    PMF (FiniteHistory Unit (CurvatureCoefficients m T R) n) :=
  finiteAdaptiveLaw (PMF.pure ()) (curvatureComparisonTransition P Θ A β R hR a₀) n

/-- The path weights are masses of a normalized probability law. -/
theorem curvatureComparisonSamplingLaw_apply (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β R : ℝ) (hR : 2≤R)
    (a₀ : CurvatureCoefficients m T R) :
    ∀ n h, curvatureComparisonSamplingLaw P Θ A β R hR a₀ n h=
      curvatureComparisonWeight P Θ A β R hR (finiteHistoryTape a₀ n h) n := by
  intro n
  induction n with
  | zero => intro h; cases h; simp [curvatureComparisonSamplingLaw, curvatureComparisonWeight]
  | succ n ih =>
    intro h
    change curvatureComparisonSamplingLaw P Θ A β R hR a₀ n h.1 *
      curvatureComparisonTransition P Θ A β R hR a₀ n h.1 h.2 = _
    rw [ih, curvatureComparisonWeight]
    have ht : ∀ t, t<n → finiteHistoryTape a₀ (n+1) h t=finiteHistoryTape a₀ n h.1 t :=
      finiteHistoryTape_succ_lt a₀ n h
    rw [curvatureComparisonWeight_tape_congr P Θ A β R hR _ _ n ht,
      curvatureComparisonIndex_tape_congr P Θ A β _ _ n ht, finiteHistoryTape_succ_at]
    rfl

theorem curvatureComparisonSamplingLaw_ne_zero (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β R : ℝ) (hR : 2≤R)
    (a₀ : CurvatureCoefficients m T R) (n : ℕ)
    (h : FiniteHistory Unit (CurvatureCoefficients m T R) n) :
    curvatureComparisonSamplingLaw P Θ A β R hR a₀ n h≠0 := by
  rw [curvatureComparisonSamplingLaw_apply]
  exact curvatureComparisonWeight_ne_zero P Θ A β R hR _ n

theorem curvatureComparisonSamplingLaw_default_congr (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β R : ℝ) (hR : 2≤R)
    (a₀ a₁ : CurvatureCoefficients m T R) (n : ℕ) :
    curvatureComparisonSamplingLaw P Θ A β R hR a₀ n=
      curvatureComparisonSamplingLaw P Θ A β R hR a₁ n := by
  ext h
  simp only [curvatureComparisonSamplingLaw_apply]
  exact curvatureComparisonWeight_tape_congr P Θ A β R hR _ _ n
    (finiteHistoryTape_default_congr a₀ a₁ n h)

/-- A finite entry history has the same probability after replacing all hidden
blocks at and beyond the new stage. -/
theorem curvatureStageEntry_mass_prefix (P : CurvaturePolicy m T S)
    (Θ Θ' : Fin (T+1) → BalancedVector m) (A β R : ℝ) (hR : 2≤R)
    (a₀ : CurvatureCoefficients m T R) (stage n : ℕ)
    (h : FiniteHistory Unit (CurvatureCoefficients m T R) n)
    (hΘ : ∀ i, i.val<stage → Θ i=Θ' i) :
    (if curvatureStageEntry P Θ A β (finiteHistoryTape a₀ n h) stage n
      then curvatureComparisonSamplingLaw P Θ A β R hR a₀ n h else 0)=
    (if curvatureStageEntry P Θ' A β (finiteHistoryTape a₀ n h) stage n
      then curvatureComparisonSamplingLaw P Θ' A β R hR a₀ n h else 0) := by
  simp only [curvatureComparisonSamplingLaw_apply]
  exact curvatureStageEntry_weight_prefix P Θ Θ' A β R hR _ stage n hΘ

end
end SecondOrder
