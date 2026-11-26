import Bilevel.PolishedCompiledHistoryConstructors

/-! Countable dispatch continuation kernels, with no uniform-horizon premise. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Bilevel.PolishedCompiledHistory.Summary
open OracleCode Stateful HistoryProgram PolishedHistory
set_option autoImplicit false
variable {Q O A B H : Space}
variable (p : ℕ → Machine Q O A B) (c : ℕ → Code Q O A B)
  (R : HistoryProgram.Oracle Q O H) (T : ∀ i,Summary (p i) (c i) R)
  (n : A → ℕ) (hn : Measurable n)

def chooseRemaining : Procedure (Machine.choose p n hn).state H B where
  law := {
    toFun := fun z => (T z.1.1).remaining.law (z.1.2,z.2)
    measurable' := OracleSigma.prod_elim_measurable _ (fun i => (T i).remaining.law.measurable) }
  markov := ⟨fun z => (T z.1.1).remaining.markov.isProbabilityMeasure _⟩

def chooseValid : Set (Machine.choose p n hn).state := {z | z.2∈(T z.1).valid}

theorem chooseValid_measurable : MeasurableSet (chooseValid p c R T n hn) := by
  change MeasurableSet[⨅ i,(inferInstance : MeasurableSpace (p i).state).map (Sigma.mk i)] _
  rw [MeasurableSpace.measurableSet_iInf]
  intro i
  exact (T i).valid_measurable

def choose : Summary (Machine.choose p n hn) (.choose c n hn) R where
  remaining := chooseRemaining p c R T n hn
  valid := chooseValid p c R T n hn
  valid_measurable := chooseValid_measurable p c R T n hn
  start_valid := fun a => (T (n a)).start_valid a
  update_valid := by
    rintro ⟨i,s⟩ hs o
    exact (T i).update_valid s hs o
  start_law := fun a h => (T (n a)).start_law a h
  halt_law := by
    rintro ⟨i,s⟩ hs h hh
    exact (T i).halt_law s hs h hh
  live_law := by
    rintro ⟨i,s⟩ hs h hh
    change (T i).remaining.law (s,h)=_
    rw [(T i).live_law s hs h hh]
    apply Measure.ext_of_lintegral
    intro f hf
    rw [Kernel.lintegral_map _ increment_measurable _ hf,
      Kernel.lintegral_map _ increment_measurable _ hf]
    have hu := Kernel.lintegral_comp (T i).remaining.law (HistoryProgram.liveStep (p i).program R) (s,h)
      (hf.comp increment_measurable)
    have hv := Kernel.lintegral_comp (chooseRemaining p c R T n hn).law
      (HistoryProgram.liveStep (Machine.choose p n hn).program R) (⟨i,s⟩,h)
      (hf.comp increment_measurable)
    erw [hu,hv,HistoryProgram.liveStep_apply,HistoryProgram.liveStep_apply]
    have hm : Measurable (fun z => ∫⁻ y,f (increment y) ∂(T i).remaining.law z) :=
      (hf.comp increment_measurable).lintegral_kernel
    have hk : Measurable (fun z => ∫⁻ y,f (increment y) ∂(chooseRemaining p c R T n hn).law z) :=
      (hf.comp increment_measurable).lintegral_kernel
    have ha : Measurable (fun o : O => HistoryProgram.advance (p i).program R ((s,h),o)) :=
      (HistoryProgram.advance_measurable _ _).comp (measurable_const.prodMk measurable_id)
    have hb : Measurable (fun o : O => HistoryProgram.advance (Machine.choose p n hn).program R ((⟨i,s⟩,h),o)) :=
      (HistoryProgram.advance_measurable _ _).comp (measurable_const.prodMk measurable_id)
    erw [lintegral_map hm ha,lintegral_map hk hb]
    rfl

end Bilevel.PolishedCompiledHistory.Summary
