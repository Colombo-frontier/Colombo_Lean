import Bilevel.PolishedCompiledHistorySummary

/-! Constructing continuation summaries for causal-code compiler constructors. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Bilevel.PolishedCompiledHistory
open OracleCode Stateful HistoryProgram PolishedHistory
set_option autoImplicit false
variable {Q O A B C H : Space}

namespace Summary

def pure (R : HistoryProgram.Oracle Q O H) (q₀ : Q) (f : A → B) (hf : Measurable f) :
    Summary (Machine.pure q₀ f hf) (.pure f hf) R where
  remaining := Procedure.pure f hf
  valid := Set.univ
  valid_measurable := MeasurableSet.univ
  start_valid := fun _ => Set.mem_univ _
  update_valid := fun _ _ _ => Set.mem_univ _
  start_law := fun _ _ => rfl
  halt_law := fun _ _ _ _ => rfl
  live_law := by intro s _ h hh;cases hh

def reparam {I : Space} {m : Machine Q O A B} {c : Code Q O A B}
    {R : HistoryProgram.Oracle Q O H} (T : Summary m c R) (f : I → A) (hf : Measurable f) :
    Summary (Machine.reparam m f hf) (.reparam c f hf) R where
  remaining := T.remaining
  valid := T.valid
  valid_measurable := T.valid_measurable
  start_valid := fun a => T.start_valid (f a)
  update_valid := T.update_valid
  start_law := fun a h => T.start_law (f a) h
  halt_law := T.halt_law
  live_law := T.live_law

/-- Integrating a measurable nonnegative test through the stateful bind. -/
theorem lintegral_bind (P : Procedure A H B) (T : Procedure (prod A B) H C)
    (a : A) (h : H) (f : Outcome C H → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ y,f y ∂(P.bind T).law (a,h))=
      ∫⁻ z,∫⁻ y,f (Procedure.combine (z,y)) ∂T.law ((a,z.1),z.2.1) ∂P.law (a,h) := by
  rw [Procedure.bind_law_eq,lintegral_map hf Procedure.combine_measurable]
  exact Measure.lintegral_compProd (hf.comp Procedure.combine_measurable)

open Classical in
def callRemaining (R : HistoryProgram.Oracle Q O H) (o₀ : O) :
    Procedure (Machine.call (Q:=Q) o₀).state H O where
  law := Kernel.piecewise
    ((measurable_fst.comp (measurable_snd.comp measurable_fst)) (measurableSet_singleton true))
    (Procedure.pure (fun z : Q×Bool×O => z.2.2) (measurable_snd.comp measurable_snd)).law
    ((OracleCode.History.call R.law R.update R.update_measurable).reparam
      (fun z : Q×Bool×O => z.1) measurable_fst).law
  markov := by infer_instance

theorem callRemaining_live (R : HistoryProgram.Oracle Q O H) (o₀ : O)
    (q : Q) (o : O) (h : H) :
    (callRemaining R o₀).law ((q,false,o),h)=
      (OracleCode.History.call R.law R.update R.update_measurable).law (q,h) := by
  simp only [callRemaining,Kernel.piecewise_apply,Set.mem_setOf_eq,Set.mem_preimage,Set.mem_singleton_iff,Function.comp_apply,Prod.fst,Prod.snd,
    Bool.false_eq_true,if_false,Procedure.reparam,Kernel.comap_apply]

theorem callRemaining_halt (R : HistoryProgram.Oracle Q O H) (o₀ : O)
    (q : Q) (o : O) (h : H) :
    (callRemaining R o₀).law ((q,true,o),h)=Measure.dirac (o,h,0) := by
  simp only [callRemaining,Kernel.piecewise_apply,Set.mem_setOf_eq,Set.mem_preimage,Set.mem_singleton_iff,Function.comp_apply,Prod.fst,Prod.snd,
    if_true,Procedure.pure_law]
  rfl

def call (R : HistoryProgram.Oracle Q O H) (o₀ : O) :
    Summary (Machine.call (Q:=Q) o₀) (.call) R where
  remaining := callRemaining R o₀
  valid := Set.univ
  valid_measurable := MeasurableSet.univ
  start_valid := fun _ => Set.mem_univ _
  update_valid := fun _ _ _ => Set.mem_univ _
  start_law := fun q h => callRemaining_live R o₀ q o₀ h
  halt_law := by
    rintro ⟨q,b,o⟩ _ h hh
    change b=true at hh
    subst b
    exact callRemaining_halt R o₀ q o h
  live_law := by
    rintro ⟨q,b,o⟩ _ h hh
    change b=false at hh
    subst b
    rw [callRemaining_live,OracleCode.History.call_law]
    apply Measure.ext_of_lintegral
    intro f hf
    have hout : Measurable (fun obs : O => (obs,R.update ((q,h),obs),(1:ℕ))) :=
      measurable_id.prodMk ((R.update_measurable.comp (measurable_const.prodMk measurable_id)).prodMk measurable_const)
    have hadv : Measurable (fun obs : O => HistoryProgram.advance (Machine.call (Q:=Q) o₀).program R (((q,false,o),h),obs)) :=
      (HistoryProgram.advance_measurable _ _).comp (measurable_const.prodMk measurable_id)
    have hinner : Measurable (fun z => ∫⁻ y,f (increment y) ∂(callRemaining R o₀).law z) :=
      (hf.comp increment_measurable).lintegral_kernel
    rw [lintegral_map hf hout,Kernel.lintegral_map _ increment_measurable _ hf]
    rw [show (∫⁻ y,f (increment y) ∂((callRemaining R o₀).law ∘ₖ liveStep (Machine.call (Q:=Q) o₀).program R) ((q,false,o),h))=
      ∫⁻ z,∫⁻ y,f (increment y) ∂(callRemaining R o₀).law z ∂liveStep (Machine.call (Q:=Q) o₀).program R ((q,false,o),h) from
        Kernel.lintegral_comp _ _ _ (hf.comp increment_measurable),HistoryProgram.liveStep_apply,
      lintegral_map hinner hadv]
    apply lintegral_congr
    intro obs
    change f (obs,R.update ((q,h),obs),1)=
      ∫⁻ y,f (increment y) ∂(callRemaining R o₀).law ((q,true,obs),R.update ((q,h),obs))
    rw [callRemaining_halt]
    simpa only [increment,Nat.zero_add] using
      (lintegral_dirac' (obs,R.update ((q,h),obs),0)
        (show Measurable (fun y => f (increment y)) from hf.comp increment_measurable)).symm

end Summary
end Bilevel.PolishedCompiledHistory
