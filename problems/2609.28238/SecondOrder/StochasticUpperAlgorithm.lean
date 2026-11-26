import SecondOrder.BranchedOja
import SecondOrder.BudgetedOracleTrace

open MeasureTheory
open scoped Classical ENNReal

namespace SecondOrder
noncomputable section

abbrev StochasticUpperTape (Ω : Type*) (d : ℕ) (P : Parameters) (ν ε γ : ℝ) :=
  let M := physicalCap P ν (ε/10) γ
  let δ := localFailureTolerance M
  FiniteTrackingTape Ω (BranchedOjaDraws Ω d P γ δ) P (trackingTreeDepth M) (ε/10) δ M × (Fin M → Bool)

def stochasticUpperCap (P : Parameters) (ν : ℝ) (d : ℕ) (ε γ : ℝ) : ℕ :=
  selectedQueryCap P ν (ε/10) γ
    (branchedOjaQueryCount P d γ (localFailureTolerance (physicalCap P ν (ε/10) γ)))

def stochasticUpperCoefficient (P : Parameters) (ν : ℝ) (d : ℕ) : ℝ :=
  epsilonQueryCoefficient P ν (ojaSelectedPriceCoefficient P ν d)

def stochasticUpperRun {Ω : Type*} {d : ℕ} (P : Parameters) (ν : ℝ)
    (f : Ω → Point d → ℝ) (ε γ : ℝ) (w : StochasticUpperTape Ω d P ν ε γ) :
    QueryBudgetState (TrackedState d (trackingTreeDepth (physicalCap P ν (ε/10) γ))) :=
  let δ := localFailureTolerance (physicalCap P ν (ε/10) γ)
  selectedBudgetedRun P ν (ε/10) γ (branchedOjaQueryCount P d γ δ) f
    (fun x => branchedOjaReply P f x γ δ) w

def stochasticUpperLaw {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Parameters) (ν : ℝ) (d : ℕ) (ε : ℝ) {γ : ℝ} (hγ : 0 < γ) :
    Measure (StochasticUpperTape Ω d P ν ε γ) :=
  let M := physicalCap P ν (ε/10) γ
  let δ := localFailureTolerance M
  (finiteTrackingLaw μ (branchedOjaLaw μ P d hγ δ) P (trackingTreeDepth M) (ε/10) δ M).prod (signLaw M)

instance stochasticUpperLaw_probability {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (P : Parameters) (ν : ℝ) (d : ℕ) (ε : ℝ) {γ : ℝ} (hγ : 0 < γ) :
    IsProbabilityMeasure (stochasticUpperLaw μ P ν d ε hγ) := by
  unfold stochasticUpperLaw
  infer_instance

/-- All permitted queries actually scheduled by the budgeted run, with
the same histories, candidates, line locations and fresh batches. -/
def stochasticUpperTrace {Ω : Type*} {d : ℕ} (P : Parameters) (ν : ℝ)
    (f : Ω → Point d → ℝ) (ε γ : ℝ) (w : StochasticUpperTape Ω d P ν ε γ) : List (Ω × HvpQuery d) :=
  let M := physicalCap P ν (ε/10) γ
  let δ := localFailureTolerance M
  let κ := branchedOjaQueryCount P d γ δ
  budgetedOracleRunTrace P f (trackingEpochLength P (ε/10)) (stochasticUpperCap P ν d ε γ) κ
    P.gradientLip (curvatureRadius P.hessianHolder ν γ) (ε/10) (trackingChordTolerance (ε/10) M) δ
    (fun x => branchedOjaReply P f x γ δ) (fun x => branchedOjaTrace P f x γ δ)
    w.1.1 (extendSigns w.2) M w.1.2

theorem stochasticUpperTrace_price {Ω : Type*} {d : ℕ} (P : Parameters) (ν : ℝ)
    (f : Ω → Point d → ℝ) (ε γ : ℝ) (w : StochasticUpperTape Ω d P ν ε γ) :
    (stochasticUpperTrace P ν f ε γ w).length ≤ (stochasticUpperRun P ν f ε γ w).2.1 :=
  budgetedOracleRunTrace_price P f (trackingEpochLength P (ε/10)) (stochasticUpperCap P ν d ε γ)
    (branchedOjaQueryCount P d γ _) P.gradientLip (curvatureRadius P.hessianHolder ν γ) (ε/10)
    (trackingChordTolerance (ε/10) (physicalCap P ν (ε/10) γ)) _
    (fun x => branchedOjaReply P f x γ _) (fun x => branchedOjaTrace P f x γ _)
    (fun x w => branchedOjaTrace_length_le P f x γ _ w)
    w.1.1 (extendSigns w.2) (physicalCap P ν (ε/10) γ) w.1.2

theorem stochasticUpperRun_spent_le {Ω : Type*} {d : ℕ} (P : Parameters) (ν : ℝ)
    (f : Ω → Point d → ℝ) (ε γ : ℝ) (w : StochasticUpperTape Ω d P ν ε γ) :
    (stochasticUpperRun P ν f ε γ w).2.1 ≤ stochasticUpperCap P ν d ε γ :=
  selectedBudgetedRun_spent_le P ν (ε/10) γ (branchedOjaQueryCount P d γ _) f
    (fun x => branchedOjaReply P f x γ _) w

theorem stochasticUpperTrace_cap {Ω : Type*} {d : ℕ} (P : Parameters) (ν : ℝ)
    (f : Ω → Point d → ℝ) (ε γ : ℝ) (w : StochasticUpperTape Ω d P ν ε γ) :
    (stochasticUpperTrace P ν f ε γ w).length ≤ stochasticUpperCap P ν d ε γ :=
  (stochasticUpperTrace_price P ν f ε γ w).trans (stochasticUpperRun_spent_le P ν f ε γ w)

theorem stochasticUpperCap_rate (P : Parameters) (d : ℕ) {ν ε γ : ℝ}
    (hν : 0 < ν) (hε : 0 < ε) (hε1 : ε ≤ 1) (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    (stochasticUpperCap P ν d ε γ:ℝ) <
      stochasticUpperCoefficient P ν d*(toleranceLog ε γ)^4*holderEndpointRate ν ε γ :=
  selectedQueryCap_epsilon_rate P hν hε hε1 hγ hγ1 (ojaSelectedPriceCoefficient_pos P hν d).le
    (branchedOjaQueryCount_rate P d hν hε hε1 hγ hγ1)

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {P : Parameters} {ν : ℝ}
  {F : Point d → ℝ} {f : Ω → Point d → ℝ}

theorem CommonLoss.stochasticUpperRun_measurable (h : CommonLoss μ P ν F f) (ε γ : ℝ) :
    Measurable (stochasticUpperRun P ν f ε γ) :=
  h.selectedBudgetedRun_measurable (ε/10) γ (branchedOjaQueryCount P d γ _)
    (h.branchedOjaReply_measurable γ _)

theorem CommonLoss.stochasticUpperRun_success (h : CommonLoss μ P ν F f)
    {ε γ : ℝ} (hε : 0 < ε) (hγ : 0 < γ) :
    ENNReal.ofReal (29/32:ℝ) ≤ stochasticUpperLaw μ P ν d ε hγ
      {w | BudgetedSuccess F ε γ (stochasticUpperRun P ν f ε γ w)} := by
  let M := physicalCap P ν (ε/10) γ
  let δ := localFailureTolerance M
  let routine : Point d → BranchedOjaDraws Ω d P γ δ → CurvatureReply d :=
    fun x => branchedOjaReply P f x γ δ
  have hm : Measurable (fun w : Point d × BranchedOjaDraws Ω d P γ δ => routine w.1 w.2) :=
    h.branchedOjaReply_measurable γ δ
  have hc : ∀ x, branchedOjaLaw μ P d hγ δ
      {w | ¬ ValidCurvatureReply F γ x (routine x w)} ≤ ENNReal.ofReal δ := by
    intro x
    simp_rw [validCurvatureReply_iff_rayleigh]
    exact h.branchedOjaReply_confidence hγ (localFailureTolerance_pos M) (localFailureTolerance_le_one M) x
  exact h.selectedBudgetedRun_epsilon_success (η := branchedOjaLaw μ P d hγ δ)
    (routine := routine) hε hγ hm hc (branchedOjaQueryCount P d γ δ)

/-- A concrete all-dimension algorithm with no supplied eigensolver or
price assumption: every query path obeys the stated bound, and the
measurable output is an SOSP with probability at least 29/32. -/
theorem CommonLoss.stochasticUpperRun_rate (h : CommonLoss μ P ν F f)
    {ε γ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    (∀ w : StochasticUpperTape Ω d P ν ε γ,
      ((stochasticUpperTrace P ν f ε γ w).length:ℝ) <
        stochasticUpperCoefficient P ν d*(toleranceLog ε γ)^4*holderEndpointRate ν ε γ) ∧
    ENNReal.ofReal (29/32:ℝ) ≤ stochasticUpperLaw μ P ν d ε hγ
      {w | BudgetedSuccess F ε γ (stochasticUpperRun P ν f ε γ w)} := by
  refine ⟨?_, h.stochasticUpperRun_success hε hγ⟩
  intro w
  have hb : ((stochasticUpperTrace P ν f ε γ w).length:ℝ) ≤ stochasticUpperCap P ν d ε γ := by
    exact_mod_cast stochasticUpperTrace_cap P ν f ε γ w
  exact hb.trans_lt (stochasticUpperCap_rate P d h.nu_pos hε hε1 hγ hγ1)

end
end SecondOrder
