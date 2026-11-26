import Bilevel.PolishedCompiledHistoryConstructors

/-! Exact continuation semantics of the compiler's normalized bind. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Bilevel.PolishedCompiledHistory.Summary
open OracleCode Stateful HistoryProgram PolishedHistory
set_option autoImplicit false
variable {Q O A B C H : Space}
variable {p : Machine Q O A B} {q : Machine Q O (prod A B) C}
  {cp : Code Q O A B} {cq : Code Q O (prod A B) C} {R : HistoryProgram.Oracle Q O H}
  (T : Summary p cp R) (U : Summary q cq R)

def leftContinuation : Procedure (A×p.state) H C :=
  (T.remaining.reparam (fun z : A×p.state => z.2) measurable_snd).bind
    ((OracleCode.History.denote R.law R.update R.update_measurable cq).reparam
      (fun z : (A×p.state)×B => (z.1.1,z.2))
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd))

def bindRemaining : Procedure (Machine.bind p q).state H C where
  law := {
    toFun := fun z => match z.1 with
      | Sum.inl a => (leftContinuation (cq:=cq) T).law (a,z.2)
      | Sum.inr s => U.remaining.law (s,z.2)
    measurable' := by
      have hm := (leftContinuation (cq:=cq) T).law.measurable.sumElim U.remaining.law.measurable
      convert hm.comp (MeasurableEquiv.sumProdDistrib (A×p.state) q.state H).measurable using 1
      funext z
      rcases z with ⟨s,h⟩
      cases s <;> rfl }
  markov := ⟨fun z => by rcases z with ⟨s,h⟩;cases s <;> dsimp <;> infer_instance⟩

def bindValid : Set (Machine.bind p q).state :=
  {s | match s with
    | Sum.inl z => z.2∈T.valid ∧ p.program.halt z.2=false
    | Sum.inr v => v∈U.valid}

theorem bindValid_measurable : MeasurableSet (bindValid T U) := by
  rw [measurableSet_sum_iff]
  constructor
  · exact (T.valid_measurable.preimage measurable_snd).inter
      ((p.program.halt_measurable.comp measurable_snd) (measurableSet_singleton false))
  · exact U.valid_measurable

theorem enter_valid (a : A) (s : p.state) (hs : s∈T.valid) :
    Machine.enter p q (a,s)∈bindValid T U := by
  cases hh : p.program.halt s with
  | false =>
      simp only [Machine.enter,hh,Bool.false_eq_true,if_false]
      exact show s∈T.valid ∧ p.program.halt s=false from ⟨hs,hh⟩
  | true =>
      simp only [Machine.enter,hh,if_true]
      exact U.start_valid (a,p.program.output s)

/-- Integral form of the left continuation, with the full hidden history
and the two actual call counters threaded by the same bind. -/
theorem leftContinuation_integral (a : A) (s : p.state) (h : H)
    (f : Outcome C H → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ y,f y ∂(leftContinuation (cq:=cq) T).law ((a,s),h))=
      ∫⁻ z,∫⁻ y,f (Procedure.combine (z,y))
        ∂(OracleCode.History.denote R.law R.update R.update_measurable cq).law ((a,z.1),z.2.1)
        ∂T.remaining.law (s,h) := by
  unfold leftContinuation
  exact lintegral_bind (A:=of (A×p.state)) (B:=B) (C:=C) _ _ (a,s) h f hf

theorem left_inner_measurable (a : A) (f : Outcome C H → ℝ≥0∞) (hf : Measurable f) :
    Measurable (fun z : Outcome B H => ∫⁻ y,f (Procedure.combine (z,y))
      ∂(OracleCode.History.denote R.law R.update R.update_measurable cq).law ((a,z.1),z.2.1)) := by
  exact (hf.comp Procedure.combine_measurable).lintegral_kernel_prod_right'
    (κ:=Procedure.continuation (OracleCode.History.denote R.law R.update R.update_measurable cq) a)

theorem enter_law (a : A) (s : p.state) (hs : s∈T.valid) (h : H) :
    (bindRemaining T U).law (Machine.enter p q (a,s),h)=(leftContinuation (cq:=cq) T).law ((a,s),h) := by
  cases hh : p.program.halt s with
  | false =>
      simp only [Machine.enter,hh,Bool.false_eq_true,if_false,bindRemaining]
      rfl
  | true =>
      simp only [Machine.enter,hh,if_true,bindRemaining]
      change U.remaining.law (q.start (a,p.program.output s),h)=_
      rw [U.start_law]
      symm
      apply Measure.ext_of_lintegral
      intro f hf
      rw [leftContinuation_integral (cq:=cq) T a s h f hf,T.halt_law s hs h hh,
        lintegral_dirac' _ (left_inner_measurable (cq:=cq) a f hf)]
      apply lintegral_congr
      intro y
      simp only [Procedure.combine,Nat.zero_add,Prod.eta]

def bind : Summary (Machine.bind p q) (.bind cp cq) R where
  remaining := bindRemaining T U
  valid := bindValid T U
  valid_measurable := bindValid_measurable T U
  start_valid := fun a => enter_valid T U a (p.start a) (T.start_valid a)
  update_valid := by
    intro s hs o
    cases s with
    | inl z =>
        change Machine.enter p q (z.1,p.program.update (z.2,o))∈bindValid T U
        exact enter_valid T U z.1 (p.program.update (z.2,o)) (T.update_valid z.2 hs.1 o)
    | inr s => exact U.update_valid s hs o
  start_law := by
    intro a h
    change (bindRemaining T U).law (Machine.enter p q (a,p.start a),h)=_
    rw [enter_law T U a (p.start a) (T.start_valid a) h]
    apply Measure.ext_of_lintegral
    intro f hf
    rw [leftContinuation_integral (cq:=cq) T a (p.start a) h f hf,T.start_law,
      OracleCode.History.denote,lintegral_bind _ _ _ _ f hf]
  halt_law := by
    intro s hs h hh
    cases s with
    | inl z => cases hh
    | inr s => exact U.halt_law s hs h hh
  live_law := by
    intro s hs h hh
    cases s with
    | inr s =>
        change U.remaining.law (s,h)=_
        rw [U.live_law s hs h hh]
        apply Measure.ext_of_lintegral
        intro f hf
        rw [Kernel.lintegral_map _ increment_measurable _ hf,
          Kernel.lintegral_map _ increment_measurable _ hf]
        have hu := Kernel.lintegral_comp U.remaining.law (HistoryProgram.liveStep q.program R) (s,h)
          (hf.comp increment_measurable)
        have hv := Kernel.lintegral_comp (bindRemaining T U).law
          (HistoryProgram.liveStep (Machine.bind p q).program R) (Sum.inr s,h)
          (hf.comp increment_measurable)
        erw [hu,hv,HistoryProgram.liveStep_apply,HistoryProgram.liveStep_apply]
        have hm : Measurable (fun z => ∫⁻ y,f (increment y) ∂U.remaining.law z) :=
          (hf.comp increment_measurable).lintegral_kernel
        have hn : Measurable (fun z => ∫⁻ y,f (increment y) ∂(bindRemaining T U).law z) :=
          (hf.comp increment_measurable).lintegral_kernel
        have ha : Measurable (fun o : O => HistoryProgram.advance q.program R ((s,h),o)) :=
          (HistoryProgram.advance_measurable _ _).comp (measurable_const.prodMk measurable_id)
        have hb : Measurable (fun o : O => HistoryProgram.advance (Machine.bind p q).program R ((Sum.inr s,h),o)) :=
          (HistoryProgram.advance_measurable _ _).comp (measurable_const.prodMk measurable_id)
        erw [lintegral_map hm ha,lintegral_map hn hb]
        rfl
    | inl z =>
        change (leftContinuation (cq:=cq) T).law (z,h)=_
        apply Measure.ext_of_lintegral
        intro f hf
        rw [leftContinuation_integral (cq:=cq) T z.1 z.2 h f hf,
          T.remaining_live_integral _ (left_inner_measurable (cq:=cq) z.1 f hf) z.2 hs.1 h hs.2,
          Kernel.lintegral_map _ increment_measurable _ hf]
        have hcomp := Kernel.lintegral_comp (bindRemaining T U).law
          (HistoryProgram.liveStep (Machine.bind p q).program R) (Sum.inl z,h)
          (hf.comp increment_measurable)
        erw [hcomp,HistoryProgram.liveStep_apply]
        have hm : Measurable (fun t => ∫⁻ y,f (increment y) ∂(bindRemaining T U).law t) :=
          (hf.comp increment_measurable).lintegral_kernel
        have ha : Measurable (fun o : O => HistoryProgram.advance (Machine.bind p q).program R ((Sum.inl z,h),o)) :=
          (HistoryProgram.advance_measurable _ _).comp (measurable_const.prodMk measurable_id)
        erw [lintegral_map hm ha]
        apply lintegral_congr
        intro o
        change _=∫⁻ y,f (increment y) ∂(bindRemaining T U).law
          (Machine.enter p q (z.1,p.program.update (z.2,o)),R.update ((p.program.query z.2,h),o))
        erw [enter_law T U z.1 (p.program.update (z.2,o)) (T.update_valid z.2 hs.1 o),
          leftContinuation_integral (cq:=cq) T z.1 (p.program.update (z.2,o)) _ _ (hf.comp increment_measurable)]
        apply lintegral_congr
        intro out
        apply lintegral_congr
        intro out'
        change f (out'.1,out'.2.1,(out.2.2+1)+out'.2.2)=
          f (out'.1,out'.2.1,(out.2.2+out'.2.2)+1)
        have he : out.2.2+1+out'.2.2=out.2.2+out'.2.2+1 := by omega
        exact congrArg (fun k => f (out'.1,out'.2.1,k)) he

end Bilevel.PolishedCompiledHistory.Summary
