import SecondOrder.BudgetRunProgram
import SecondOrder.OracleProgramSeededBind
import SecondOrder.OracleProgramMapLaw
import SecondOrder.FiniteSeedExtension

open MeasureTheory ProbabilityTheory

namespace SecondOrder
noncomputable section

variable {Ω : Type} [MeasurableSpace Ω] {d L : ℕ}

def budgetStepOutputKernel (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Parameters) (q Q : ℕ) (Lip s τ ρ γ δ : ℝ)
    (η : Measure (TrackingProgramSeed d L P γ δ)) [IsProbabilityMeasure η]
    (a₀ : Ω) (reply : HvpQuery d → Ω → Point d)
    (hr : Measurable (fun w : HvpQuery d × Ω => reply w.1 w.2)) :
    Kernel (BudgetTracker d L) (BudgetTracker d L) :=
  OracleProgram.seededOutputKernel μ η (.grad 0) 0 (trackedInitial 0,0,true) a₀ reply hr
    (budgetStepProgram P q Q Lip s τ ρ γ δ)
    (budgetStepProgram_measurable P q Q Lip s τ ρ γ δ) Q

instance budgetStepOutputKernel_markov (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Parameters) (q Q : ℕ) (Lip s τ ρ γ δ : ℝ)
    (η : Measure (TrackingProgramSeed d L P γ δ)) [IsProbabilityMeasure η]
    (a₀ : Ω) (reply : HvpQuery d → Ω → Point d)
    (hr : Measurable (fun w : HvpQuery d × Ω => reply w.1 w.2)) :
    IsMarkovKernel (budgetStepOutputKernel μ P q Q Lip s τ ρ γ δ η a₀ reply hr) := by
  unfold budgetStepOutputKernel
  infer_instance

def budgetRunOutputLaw (μ : Measure Ω) (P : Parameters) (q Q : ℕ) (Lip s τ ρ γ δ : ℝ)
    (η : Measure (TrackingProgramSeed d L P γ δ)) (reply : HvpQuery d → Ω → Point d)
    (N : ℕ) : Measure (BudgetTracker d L) :=
  OracleProgram.seededOutputLaw μ (Measure.pi (fun _ : Fin N => η)) (.grad 0)
    (trackedInitial 0,0,true) reply (budgetRunProgram P q Q Lip s τ ρ γ δ N) Q

theorem budgetRunOutputLaw_zero (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Parameters) (q Q : ℕ) (Lip s τ ρ γ δ : ℝ)
    (η : Measure (TrackingProgramSeed d L P γ δ)) [IsProbabilityMeasure η]
    (a₀ : Ω) (reply : HvpQuery d → Ω → Point d)
    (hr : Measurable (fun w : HvpQuery d × Ω => reply w.1 w.2)) :
    budgetRunOutputLaw μ P q Q Lip s τ ρ γ δ η reply 0=
      OracleProgram.outputLaw μ (.grad 0) (trackedInitial 0,0,true) reply
        (budgetInitialProgram P Q τ δ) Q := by
  exact OracleProgram.seededOutputLaw_const μ (Measure.pi (fun _ : Fin 0 => η)) (.grad 0) 0
    (trackedInitial 0,0,true) a₀ reply hr (budgetInitialProgram P Q τ δ)
    (budgetInitialProgram_measurable P Q τ δ) Q

/-- Each physical step uses an independent private seed. The distribution
recursion uses the original hard cap Q, even though the proof temporarily
allows Q+Q draws to apply the general composition theorem. -/
theorem budgetRunOutputLaw_succ (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Parameters) (q Q : ℕ) (Lip s τ ρ γ δ : ℝ)
    (η : Measure (TrackingProgramSeed d L P γ δ)) [IsProbabilityMeasure η]
    (a₀ : Ω) (reply : HvpQuery d → Ω → Point d)
    (hr : Measurable (fun w : HvpQuery d × Ω => reply w.1 w.2)) (N : ℕ) :
    budgetRunOutputLaw μ P q Q Lip s τ ρ γ δ η reply (N+1)=
      (budgetRunOutputLaw μ P q Q Lip s τ ρ γ δ η reply N).bind
        (budgetStepOutputKernel μ P q Q Lip s τ ρ γ δ η a₀ reply hr) := by
  let ηN := Measure.pi (fun _ : Fin N => η)
  let ηS := Measure.pi (fun _ : Fin (N+1) => η)
  let g : ((Fin N → TrackingProgramSeed d L P γ δ) × TrackingProgramSeed d L P γ δ) →
      Fin (N+1) → TrackingProgramSeed d L P γ δ := fun w =>
    Fin.snoc w.1 w.2
  have hg := finSnoc_measurePreserving η N
  have hprog : (fun w => budgetRunProgram P q Q Lip s τ ρ γ δ (N+1) (g w))=
      (fun w : (Fin N → TrackingProgramSeed d L P γ δ) × TrackingProgramSeed d L P γ δ =>
        OracleProgram.bind (budgetRunProgram P q Q Lip s τ ρ γ δ N w.1)
          (fun z => budgetStepProgram P q Q Lip s τ ρ γ δ (z,w.2))) := by
    funext w
    simp only [g,budgetRunProgram,Fin.snoc_castSucc,Fin.snoc_last]
  have hseed := OracleProgram.seededOutputLaw_mapSeed μ (ηN.prod η) (.grad 0) 0
    ((trackedInitial 0,0,true) : BudgetTracker d L) a₀ reply hr
    (budgetRunProgram P q Q Lip s τ ρ γ δ (N+1))
    (budgetRunProgram_measurable P q Q Lip s τ ρ γ δ (N+1)) g hg.measurable (Q+Q)
  rw [hg.map_eq,hprog] at hseed
  have hfull := OracleProgram.seededOutputLaw_add_of_usesAtMost μ ηS (.grad 0) 0
    ((trackedInitial 0,0,true) : BudgetTracker d L) a₀ reply hr
    (budgetRunProgram P q Q Lip s τ ρ γ δ (N+1))
    (budgetRunProgram_measurable P q Q Lip s τ ρ γ δ (N+1)) Q
    (budgetRunProgram_usesAtMost P q Q Lip s τ ρ γ δ (N+1)) Q
  have hstep : ∀ w : BudgetStepInput d L P γ δ,
      OracleProgram.UsesAtMost Q (budgetStepProgram P q Q Lip s τ ρ γ δ w) := by
    intro w
    exact OracleProgram.usesAtMost_mono
      (budgetStepProgram_credit P q Q Lip s τ ρ γ δ w).usesAtMost (Nat.sub_le _ _)
  have hbind := OracleProgram.seededOutputLaw_bind_of_usesAtMost μ ηN η (.grad 0) 0
    ((trackedInitial 0,0,true) : BudgetTracker d L) ((trackedInitial 0,0,true) : BudgetTracker d L)
    a₀ reply hr (budgetRunProgram P q Q Lip s τ ρ γ δ N)
    (budgetRunProgram_measurable P q Q Lip s τ ρ γ δ N) Q
    (budgetRunProgram_usesAtMost P q Q Lip s τ ρ γ δ N)
    (budgetStepProgram P q Q Lip s τ ρ γ δ)
    (budgetStepProgram_measurable P q Q Lip s τ ρ γ δ) Q hstep
  exact hfull.symm.trans (hseed.trans hbind)

theorem budgetRunPointProgram_outputLaw (μ : Measure Ω)
    (P : Parameters) (q Q : ℕ) (Lip s τ ρ γ δ : ℝ)
    (η : Measure (TrackingProgramSeed d L P γ δ))
    (a₀ : Ω) (reply : HvpQuery d → Ω → Point d)
    (hr : Measurable (fun w : HvpQuery d × Ω => reply w.1 w.2)) (N : ℕ) :
    OracleProgram.seededOutputLaw μ (Measure.pi (fun _ : Fin N => η)) (.grad 0) 0 reply
      (budgetRunPointProgram P q Q Lip s τ ρ γ δ N) Q=
      Measure.map (fun z : BudgetTracker d L => z.1.physical.point)
        (budgetRunOutputLaw μ P q Q Lip s τ ρ γ δ η reply N) := by
  exact OracleProgram.seededOutputLaw_bind_done μ (Measure.pi (fun _ : Fin N => η)) (.grad 0) 0
    ((trackedInitial 0,0,true) : BudgetTracker d L) 0 a₀ reply hr
    (budgetRunProgram P q Q Lip s τ ρ γ δ N)
    (budgetRunProgram_measurable P q Q Lip s τ ρ γ δ N) Q
    (budgetRunProgram_usesAtMost P q Q Lip s τ ρ γ δ N) _
    (state_measurable_fields.mp ((tracked_measurable_fields.mp measurable_fst).1)).1

end
end SecondOrder
