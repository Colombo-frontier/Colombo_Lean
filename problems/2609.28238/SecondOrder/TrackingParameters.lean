import SecondOrder.ClippedEpoch
import SecondOrder.BudgetedExecution

open MeasureTheory
open scoped Classical ENNReal

namespace SecondOrder
noncomputable section

/-- Integer form of the manuscript's 1 + ceil(log₂(M+1)). -/
def trackingTreeDepth (M : ℕ) : ℕ := 1+Nat.clog 2 (M+1)

def trackingChordTolerance (τ : ℝ) (M : ℕ) : ℝ := τ/(4*(trackingTreeDepth M : ℝ))

theorem trackingTreeDepth_pos (M : ℕ) : 0 < trackingTreeDepth M := by unfold trackingTreeDepth; omega

theorem trackingTreeDepth_covers (M : ℕ) : M ≤ 2^trackingTreeDepth M := by
  have he := Nat.le_pow_clog (by norm_num : 1 < (2 : ℕ)) (M+1)
  have hp := Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : ℕ))
    (show Nat.clog 2 (M+1) ≤ trackingTreeDepth M by unfold trackingTreeDepth; omega)
  omega

theorem trackingChordTolerance_pos {τ : ℝ} (hτ : 0 < τ) (M : ℕ) : 0 < trackingChordTolerance τ M := by
  have hL : (0 : ℝ) < trackingTreeDepth M := Nat.cast_pos.mpr (trackingTreeDepth_pos M)
  unfold trackingChordTolerance
  positivity

theorem trackingChordTolerance_total (τ : ℝ) (M : ℕ) :
    (trackingTreeDepth M : ℝ)*trackingChordTolerance τ M = τ/4 := by
  have hL : (trackingTreeDepth M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (trackingTreeDepth_pos M).ne'
  unfold trackingChordTolerance
  field_simp
  <;> ring

def chordVarianceScale (P : Parameters) : ℝ := P.hessianNoise^2+P.gradientLip^2

theorem chordVarianceScale_pos (P : Parameters) : 0 < chordVarianceScale P :=
  add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos P.gradientLip_pos)

def epochGradientCap (P : Parameters) (τ : ℝ) : ℕ := 1+⌈P.gap*P.gradientLip/τ^2⌉₊

theorem epochGradientCap_pos (P : Parameters) (τ : ℝ) : 0 < epochGradientCap P τ := by
  unfold epochGradientCap
  omega

theorem epochGradientCap_lower (P : Parameters) (τ : ℝ) :
    1+P.gap*P.gradientLip/τ^2 ≤ (epochGradientCap P τ : ℝ) := by
  have he := Nat.le_ceil (P.gap*P.gradientLip/τ^2)
  simpa only [epochGradientCap,Nat.cast_add,Nat.cast_one] using add_le_add_left he 1

theorem epochGradientCap_upper (P : Parameters) (τ : ℝ) :
    (epochGradientCap P τ : ℝ) < 2+P.gap*P.gradientLip/τ^2 := by
  have hnonneg : 0 ≤ P.gap*P.gradientLip/τ^2 := by
    exact div_nonneg (mul_nonneg P.gap_pos.le P.gradientLip_pos.le) (sq_nonneg _)
  have he := Nat.ceil_lt_add_one hnonneg
  simp only [epochGradientCap,Nat.cast_add,Nat.cast_one]
  linarith

def preferredEpochLength (P : Parameters) (τ : ℝ) : ℝ :=
  P.gradientNoise*P.gradientLip/(τ*Real.sqrt (chordVarianceScale P))

def trackingEpochLength (P : Parameters) (τ : ℝ) : ℕ :=
  clippedCeil (epochGradientCap P τ) (preferredEpochLength P τ)

theorem preferredEpochLength_pos (P : Parameters) {τ : ℝ} (hτ : 0 < τ) :
    0 < preferredEpochLength P τ := by
  have hs := Real.sqrt_pos.mpr (chordVarianceScale_pos P)
  have hn := P.gradientNoise_pos
  have hLip := P.gradientLip_pos
  unfold preferredEpochLength
  positivity

theorem trackingEpochLength_pos (P : Parameters) (τ : ℝ) : 0 < trackingEpochLength P τ :=
  clippedCeil_pos (epochGradientCap_pos P τ) _

theorem trackingEpochLength_le (P : Parameters) (τ : ℝ) :
    trackingEpochLength P τ ≤ epochGradientCap P τ := clippedCeil_le _ _

/-- A chosen cap with all of q, L, ρ and δ fixed explicitly. The input κ
still records one supplied curvature routine's price. -/
def selectedQueryCap (P : Parameters) (ν τ γ : ℝ) (κ : ℕ) : ℕ :=
  let M := physicalCap P ν τ γ
  queryCap (trackingRequestBudget P ν τ γ (trackingChordTolerance τ M) (localFailureTolerance M)
    (trackingEpochLength P τ) (trackingTreeDepth M) κ)

/-- Fully selected finite algorithm parameters; randomness is exactly
the already verified finite product of actual samples and fair signs. -/
def selectedBudgetedRun {Ω Ψ : Type*} {d : ℕ} (P : Parameters) (ν τ γ : ℝ) (κ : ℕ)
    (f : Ω → Point d → ℝ) (routine : Point d → Ψ → CurvatureReply d)
    (w : FiniteTrackingTape Ω Ψ P (trackingTreeDepth (physicalCap P ν τ γ)) τ
      (localFailureTolerance (physicalCap P ν τ γ)) (physicalCap P ν τ γ) ×
        (Fin (physicalCap P ν τ γ) → Bool)) :=
  let M := physicalCap P ν τ γ
  finiteBudgetedRun P f (trackingEpochLength P τ) (selectedQueryCap P ν τ γ κ) κ
    P.gradientLip (curvatureRadius P.hessianHolder ν γ) τ (trackingChordTolerance τ M)
    (localFailureTolerance M) routine M w

theorem selectedBudgetedRun_spent_le {Ω Ψ : Type*} {d : ℕ} (P : Parameters) (ν τ γ : ℝ) (κ : ℕ)
    (f : Ω → Point d → ℝ) (routine : Point d → Ψ → CurvatureReply d)
    (w : FiniteTrackingTape Ω Ψ P (trackingTreeDepth (physicalCap P ν τ γ)) τ
      (localFailureTolerance (physicalCap P ν τ γ)) (physicalCap P ν τ γ) ×
        (Fin (physicalCap P ν τ γ) → Bool)) :
    (selectedBudgetedRun P ν τ γ κ f routine w).2.1 ≤ selectedQueryCap P ν τ γ κ :=
  finiteBudgetedRun_spent_le P f _ _ κ _ _ _ _ _ routine _ w

variable {Ω Ψ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ] {d : ℕ}
  {μ : Measure Ω} [IsProbabilityMeasure μ] {η : Measure Ψ} [IsProbabilityMeasure η]
  {P : Parameters} {ν : ℝ} {F : Point d → ℝ} {f : Ω → Point d → ℝ}

/-- The depth, chord-error and epoch-length side conditions have been
discharged by the concrete choices above. Only the supplied curvature
routine's measurable pointwise confidence contract remains. -/
theorem CommonLoss.selectedBudgetedRun_success (h : CommonLoss μ P ν F f)
    {τ γ : ℝ} (hτ : 0 < τ) (hγ : 0 < γ) {routine : Point d → Ψ → CurvatureReply d}
    (hm : Measurable (fun w : Point d × Ψ => routine w.1 w.2))
    (hc : ∀ x, η {w | ¬ValidCurvatureReply F γ x (routine x w)} ≤
      ENNReal.ofReal (localFailureTolerance (physicalCap P ν τ γ))) (κ : ℕ) :
    let M := physicalCap P ν τ γ
    ENNReal.ofReal (29/32 : ℝ) ≤
      ((finiteTrackingLaw μ η P (trackingTreeDepth M) τ (localFailureTolerance M) M).prod (signLaw M))
        {w | BudgetedSuccess F (10*τ) γ (selectedBudgetedRun P ν τ γ κ f routine w)} := by
  exact h.budgetedExecution_success (trackingEpochLength_pos P τ) hτ hγ
    (trackingChordTolerance_pos hτ _) (trackingChordTolerance_total τ _).le
    (trackingTreeDepth_covers _) hm hc κ

theorem CommonLoss.selectedBudgetedRun_measurable (h : CommonLoss μ P ν F f)
    (τ γ : ℝ) (κ : ℕ) {routine : Point d → Ψ → CurvatureReply d}
    (hm : Measurable (fun w : Point d × Ψ => routine w.1 w.2)) :
    Measurable (selectedBudgetedRun P ν τ γ κ f routine) :=
  h.finiteBudgetedRun_measurable _ _ κ _ _ _ _ _ hm _

theorem CommonLoss.selectedBudgetedRun_epsilon_success (h : CommonLoss μ P ν F f)
    {ε γ : ℝ} (hε : 0 < ε) (hγ : 0 < γ) {routine : Point d → Ψ → CurvatureReply d}
    (hm : Measurable (fun w : Point d × Ψ => routine w.1 w.2))
    (hc : ∀ x, η {w | ¬ValidCurvatureReply F γ x (routine x w)} ≤
      ENNReal.ofReal (localFailureTolerance (physicalCap P ν (ε/10) γ))) (κ : ℕ) :
    let M := physicalCap P ν (ε/10) γ
    ENNReal.ofReal (29/32 : ℝ) ≤
      ((finiteTrackingLaw μ η P (trackingTreeDepth M) (ε/10) (localFailureTolerance M) M).prod (signLaw M))
        {w | BudgetedSuccess F ε γ (selectedBudgetedRun P ν (ε/10) γ κ f routine w)} := by
  have he : 10*(ε/10) = ε := by ring
  simpa only [he] using h.selectedBudgetedRun_success (div_pos hε (by norm_num)) hγ hm hc κ

end
end SecondOrder
