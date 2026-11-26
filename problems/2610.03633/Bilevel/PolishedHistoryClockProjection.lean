import Bilevel.PolishedHistoryClock

/-! Erasing the public bookkeeping clock preserves all finite program-state
laws. The hidden oracle history and every original response remain unchanged. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Bilevel.PolishedHistory
set_option autoImplicit false
variable {S Q O Y H : Type*} [MeasurableSpace S] [MeasurableSpace Q]
  [MeasurableSpace O] [MeasurableSpace Y] [MeasurableSpace H]
variable (A : BorelAdaptive.Program S Q O Y) (R : HistoryProgram.Oracle Q O H)

def eraseClock (z : (S × ℕ) × H) : S × H := (z.1.1,z.2)

theorem eraseClock_measurable : Measurable (eraseClock (S:=S) (H:=H)) :=
  (measurable_fst.comp measurable_fst).prodMk measurable_snd

theorem clocked_step_map :
    (HistoryProgram.step (clockedProgram A) R).map eraseClock=
      (HistoryProgram.step A R).comap eraseClock eraseClock_measurable := by
  apply Kernel.ext
  rintro ⟨⟨s,k⟩,h⟩
  rw [Kernel.map_apply _ eraseClock_measurable,Kernel.comap_apply]
  cases hh : A.halt s with
  | true =>
      rw [HistoryProgram.step_halted _ _ _ hh,HistoryProgram.step_halted _ _ _ hh,
        Measure.map_dirac eraseClock_measurable]
  | false =>
      rw [HistoryProgram.step_live _ _ _ hh,HistoryProgram.step_live _ _ _ hh]
      have hm : Measurable (fun o : O => HistoryProgram.advance (clockedProgram A) R
          (((s,k),h),o)) :=
        (HistoryProgram.advance_measurable _ _).comp (measurable_const.prodMk measurable_id)
      rw [Measure.map_map eraseClock_measurable hm]
      rfl

theorem clocked_run_map (n : ℕ) :
    (HistoryProgram.run (clockedProgram A) R n).map eraseClock=
      (HistoryProgram.run A R n).comap eraseClock eraseClock_measurable := by
  induction n with
  | zero => rw [HistoryProgram.run_zero,HistoryProgram.run_zero,
      Kernel.id_map eraseClock_measurable,Kernel.id_comap eraseClock_measurable]
  | succ n ih =>
      rw [HistoryProgram.run_succ,Kernel.map_comp,clocked_step_map,
        ← Kernel.comp_map _ _ eraseClock_measurable,ih,
        ← Kernel.comp_deterministic_eq_comap,
        ← Kernel.comp_assoc,← HistoryProgram.run_succ,
        Kernel.comp_deterministic_eq_comap]

theorem clocked_run_endpoint (n : ℕ) (s : S) (k : ℕ) (h : H) :
    (HistoryProgram.run (clockedProgram A) R n ((s,k),h)).map eraseClock=
      HistoryProgram.run A R n (s,h) := by
  rw [← Kernel.map_apply _ eraseClock_measurable,clocked_run_map,Kernel.comap_apply]
  rfl

def eraseClockPath (w : HistoryProgram.Path (S × ℕ) H) : HistoryProgram.Path S H :=
  fun n => eraseClock (w n)

theorem eraseClockPath_measurable : Measurable (eraseClockPath (S:=S) (H:=H)) :=
  measurable_pi_iff.mpr (fun n => eraseClock_measurable.comp (measurable_pi_apply n))

omit [MeasurableSpace H] in
theorem eraseClockPath_totalCalls (w : HistoryProgram.Path (S × ℕ) H) :
    HistoryProgram.totalCalls A (eraseClockPath w)=
      HistoryProgram.totalCalls (clockedProgram A) w := rfl

omit [MeasurableSpace H] in
theorem eraseClockPath_stoppedOutput (w : HistoryProgram.Path (S × ℕ) H) :
    HistoryProgram.stoppedOutput A (eraseClockPath w)=
      HistoryProgram.stoppedOutput (clockedProgram A) w := rfl

theorem execution_dirac_endpoint (s : S) (h : H) (n : ℕ) :
    (HistoryProgram.trajectoryLaw A R (Measure.dirac s) id h).map (fun w => w n)=
      HistoryProgram.run A R n (s,h) := by
  rw [HistoryProgram.trajectoryLaw_endpoint _ _ _ _ measurable_id,
    HistoryProgram.runLaw,Measure.map_dirac (measurable_id.prodMk measurable_const),
    Measure.dirac_bind (Kernel.measurable _)]
  rfl

theorem clocked_execution_endpoint (s : S) (k : ℕ) (h : H) (n : ℕ) :
    ((HistoryProgram.trajectoryLaw (clockedProgram A) R (Measure.dirac (s,k)) id h).map
      eraseClockPath).map (fun w => w n)=
    (HistoryProgram.trajectoryLaw A R (Measure.dirac s) id h).map (fun w => w n) := by
  rw [Measure.map_map (measurable_pi_apply n) eraseClockPath_measurable]
  change (HistoryProgram.trajectoryLaw (clockedProgram A) R (Measure.dirac (s,k)) id h).map
    (fun w => eraseClock (w n))=_
  have hp : Measurable (eraseClock (S:=S) (H:=H)) := eraseClock_measurable
  have hev : Measurable (fun w : HistoryProgram.Path (S × ℕ) H => w n) := measurable_pi_apply n
  calc
    _ = ((HistoryProgram.trajectoryLaw (clockedProgram A) R
        (Measure.dirac (s,k)) id h).map (fun w => w n)).map eraseClock :=
      (Measure.map_map hp hev).symm
    _ = _ := by rw [execution_dirac_endpoint,execution_dirac_endpoint,clocked_run_endpoint]

theorem clocked_execution_step_good (s : S) (k : ℕ) (h : H)
    (v : S → ℝ) (hv : Measurable v) :
    ∀ᵐ w ∂(HistoryProgram.trajectoryLaw (clockedProgram A) R (Measure.dirac (s,k)) id h).map
      eraseClockPath,∀ n,pathStepGood A v n w := by
  apply ae_all_iff.mpr
  intro n
  apply (ae_map_iff eraseClockPath_measurable.aemeasurable
    (pathStepGood_measurable A v hv n)).mpr
  exact trajectoryLaw_step_good (clockedProgram A) R _ _ _
    (fun z => v z.1) (hv.comp measurable_fst) n

theorem clocked_execution_cost (s : S) (k : ℕ) (h : H) :
    (∫⁻ w,HistoryProgram.totalCalls A w
      ∂HistoryProgram.trajectoryLaw A R (Measure.dirac s) id h)=
    ∫⁻ w,HistoryProgram.totalCalls (clockedProgram A) w
      ∂HistoryProgram.trajectoryLaw (clockedProgram A) R (Measure.dirac (s,k)) id h := by
  have hl : ∀ᵐ w ∂HistoryProgram.trajectoryLaw A R (Measure.dirac s) id h,
      ∀ n,pathStepGood A (fun _ => (0:ℝ)) n w := by
    apply ae_all_iff.mpr
    intro n
    exact trajectoryLaw_step_good A R _ _ _ _ measurable_const n
  have hr := clocked_execution_step_good A R s k h (fun _ => (0:ℝ)) measurable_const
  have he := totalCalls_integral_eq A _ _
    (fun n => (clocked_execution_endpoint A R s k h n).symm)
    (hl.mono (fun _ hw n hn => (hw n hn).1))
    (hr.mono (fun _ hw n hn => (hw n hn).1))
  exact he.trans (lintegral_map (HistoryProgram.totalCalls_measurable A) eraseClockPath_measurable)

theorem clocked_execution_risk (s : S) (k : ℕ) (h : H)
    (loss : Y → ℝ) (hloss : Measurable loss)
    (hcost : (∫⁻ w,HistoryProgram.totalCalls A w
      ∂HistoryProgram.trajectoryLaw A R (Measure.dirac s) id h)≠⊤) :
    (∫⁻ w,ENNReal.ofReal (loss (HistoryProgram.stoppedOutput A w))
      ∂HistoryProgram.trajectoryLaw A R (Measure.dirac s) id h)=
    ∫⁻ w,ENNReal.ofReal (loss (HistoryProgram.stoppedOutput (clockedProgram A) w))
      ∂HistoryProgram.trajectoryLaw (clockedProgram A) R (Measure.dirac (s,k)) id h := by
  let v := loss ∘ A.output
  have hv : Measurable v := hloss.comp A.output_measurable
  have hl : ∀ᵐ w ∂HistoryProgram.trajectoryLaw A R (Measure.dirac s) id h,
      ∀ n,pathStepGood A v n w := by
    apply ae_all_iff.mpr
    intro n
    exact trajectoryLaw_step_good A R _ _ _ _ hv n
  have hr := clocked_execution_step_good A R s k h v hv
  have he := stoppedValue_integral_eq A _ _
    (fun n => (clocked_execution_endpoint A R s k h n).symm) v hv hl hr hcost
  have hm : Measurable (fun w : HistoryProgram.Path S H =>
      ENNReal.ofReal (loss (HistoryProgram.stoppedOutput A w))) :=
    (hloss.comp (HistoryProgram.stoppedOutput_measurable A)).ennreal_ofReal
  exact he.trans (lintegral_map hm eraseClockPath_measurable)

end Bilevel.PolishedHistory
