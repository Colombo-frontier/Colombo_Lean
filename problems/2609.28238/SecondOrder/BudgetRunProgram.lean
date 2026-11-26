import SecondOrder.BudgetStepProgram

open MeasureTheory
open scoped Classical

namespace SecondOrder
noncomputable section

def budgetInitialProgram {d L : ℕ} (P : Parameters) (Q : ℕ) (τ δ : ℝ) :
    OracleProgram (HvpQuery d) (Point d) (BudgetTracker d L) :=
  if localQueryCount (P.gradientNoise^2) (τ/4) δ≤Q then
    OracleProgram.bind (gradientAnchorProgram P 0 (τ/4) δ)
      (fun a => .done (trackedInitial a,localQueryCount (P.gradientNoise^2) (τ/4) δ,false))
  else .done (trackedInitial 0,0,true)

theorem budgetInitialProgram_measurable {d L : ℕ} (P : Parameters) (Q : ℕ) (τ δ : ℝ) :
    OracleProgram.MeasurableFamily (.grad 0) (trackedInitial 0,0,true)
      (fun _ : Unit => @budgetInitialProgram d L P Q τ δ) := by
  unfold budgetInitialProgram
  split_ifs
  · have hp := (gradientAnchorProgram_measurable (d := d) P (τ/4) δ).comp
      (fun _ : Unit => (0 : Point d)) measurable_const
    apply hp.bind
    apply OracleProgram.measurableFamily_done
    exact (trackedInitial_measurable measurable_snd).prodMk measurable_const
  · exact OracleProgram.measurableFamily_done (Y := Point d) (HvpQuery.grad (0 : Point d))
      ((trackedInitial 0,0,true) : BudgetTracker d L)
      (fun _ : Unit => ((trackedInitial 0,0,true) : BudgetTracker d L)) measurable_const

theorem budgetInitialProgram_credit {d L : ℕ} (P : Parameters) (Q : ℕ) (τ δ : ℝ) :
    OracleProgram.UsesWithCredit Q (@budgetInitialProgram d L P Q τ δ) (fun z => Q-z.2.1) := by
  unfold budgetInitialProgram
  split_ifs with hc
  · have hp := (localReplyProgram_usesExactly (d := d) (P.gradientNoise^2) (τ/4) δ
      (fun _ => HvpQuery.grad (0 : Point d))).usesAtMost
    have hh := OracleProgram.usesAtMost_bind_credit hp
      (fun a => .done (trackedInitial (L := L) a,localQueryCount (P.gradientNoise^2) (τ/4) δ,false))
      (fun z : BudgetTracker d L => Q-z.2.1)
      (m := Q-localQueryCount (P.gradientNoise^2) (τ/4) δ) (fun _ => Nat.le_refl _)
    exact hh.mono (by omega)
  · exact Nat.sub_le _ _

/-- Compile the finite physical-time loop. Each continuation receives the
previous state through replies; all private seeds are chosen independently
of the unknown loss and its sample space. -/
def budgetRunProgram {d L : ℕ} (P : Parameters) (q Q : ℕ) (Lip s τ ρ γ δ : ℝ) :
    (N : ℕ) → (Fin N → TrackingProgramSeed d L P γ δ) →
      OracleProgram (HvpQuery d) (Point d) (BudgetTracker d L)
  | 0, _ => budgetInitialProgram P Q τ δ
  | N+1, seeds => OracleProgram.bind
      (budgetRunProgram P q Q Lip s τ ρ γ δ N (fun i => seeds i.castSucc))
      (fun z => budgetStepProgram P q Q Lip s τ ρ γ δ (z,seeds (Fin.last N)))

theorem budgetRunProgram_measurable {d L : ℕ} (P : Parameters) (q Q : ℕ)
    (Lip s τ ρ γ δ : ℝ) (N : ℕ) :
    OracleProgram.MeasurableFamily (.grad 0) (trackedInitial 0,0,true)
      (@budgetRunProgram d L P q Q Lip s τ ρ γ δ N) := by
  induction N with
  | zero =>
    exact (budgetInitialProgram_measurable P Q τ δ).comp
      (fun _ : Fin 0 → TrackingProgramSeed d L P γ δ => ()) measurable_const
  | succ N ih =>
    have hp := ih.comp (fun seeds : Fin (N+1) → TrackingProgramSeed d L P γ δ =>
      fun i : Fin N => seeds i.castSucc) (measurable_pi_lambda _ (fun i => measurable_pi_apply i.castSucc))
    apply hp.bind
    exact (budgetStepProgram_measurable P q Q Lip s τ ρ γ δ).comp
      (fun w : (Fin (N+1) → TrackingProgramSeed d L P γ δ) × BudgetTracker d L =>
        (w.2,w.1 (Fin.last N)))
      (measurable_snd.prodMk ((measurable_pi_apply (Fin.last N)).comp measurable_fst))

theorem budgetRunProgram_credit {d L : ℕ} (P : Parameters) (q Q : ℕ)
    (Lip s τ ρ γ δ : ℝ) (N : ℕ) (seeds : Fin N → TrackingProgramSeed d L P γ δ) :
    OracleProgram.UsesWithCredit Q (budgetRunProgram P q Q Lip s τ ρ γ δ N seeds)
      (fun z => Q-z.2.1) := by
  induction N with
  | zero => exact budgetInitialProgram_credit P Q τ δ
  | succ N ih =>
    exact (ih (fun i => seeds i.castSucc)).bind
      (fun z => budgetStepProgram P q Q Lip s τ ρ γ δ (z,seeds (Fin.last N)))
      (fun z => Q-z.2.1) (fun z => budgetStepProgram_credit P q Q Lip s τ ρ γ δ (z,seeds (Fin.last N)))

theorem budgetRunProgram_usesAtMost {d L : ℕ} (P : Parameters) (q Q : ℕ)
    (Lip s τ ρ γ δ : ℝ) (N : ℕ) (seeds : Fin N → TrackingProgramSeed d L P γ δ) :
    OracleProgram.UsesAtMost Q (budgetRunProgram P q Q Lip s τ ρ γ δ N seeds) :=
  (budgetRunProgram_credit P q Q Lip s τ ρ γ δ N seeds).usesAtMost

def budgetRunPointProgram {d L : ℕ} (P : Parameters) (q Q : ℕ)
    (Lip s τ ρ γ δ : ℝ) (N : ℕ) (seeds : Fin N → TrackingProgramSeed d L P γ δ) :
    OracleProgram (HvpQuery d) (Point d) (Point d) :=
  OracleProgram.bind (budgetRunProgram P q Q Lip s τ ρ γ δ N seeds)
    (fun z => .done z.1.physical.point)

theorem budgetRunPointProgram_measurable {d L : ℕ} (P : Parameters) (q Q : ℕ)
    (Lip s τ ρ γ δ : ℝ) (N : ℕ) :
    OracleProgram.MeasurableFamily (.grad 0) 0
      (@budgetRunPointProgram d L P q Q Lip s τ ρ γ δ N) := by
  apply (budgetRunProgram_measurable P q Q Lip s τ ρ γ δ N).bind
  apply OracleProgram.measurableFamily_done
  exact (state_measurable_fields.mp ((tracked_measurable_fields.mp measurable_snd.fst).1)).1

theorem budgetRunPointProgram_usesAtMost {d L : ℕ} (P : Parameters) (q Q : ℕ)
    (Lip s τ ρ γ δ : ℝ) (N : ℕ) (seeds : Fin N → TrackingProgramSeed d L P γ δ) :
    OracleProgram.UsesAtMost Q (budgetRunPointProgram P q Q Lip s τ ρ γ δ N seeds) := by
  have hh := OracleProgram.usesAtMost_bind
    (budgetRunProgram_usesAtMost P q Q Lip s τ ρ γ δ N seeds)
    (fun z => .done z.1.physical.point) (m := 0) (fun _ => trivial)
  simpa only [Nat.add_zero] using hh

end
end SecondOrder
