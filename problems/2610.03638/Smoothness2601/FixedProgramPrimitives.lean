import Smoothness2601.FixedProgramComposition

/-! Semantic laws for public pure instructions, original oracle calls and
deterministic input/output transformations. -/
noncomputable section
open MeasureTheory ProbabilityTheory Bilevel.Stateful
open scoped ENNReal
namespace Smoothness2601.FixedProgram.Program

theorem procedure_ext {A B H : Type} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace H]
    (P Q : Procedure A H B) (h : P.law = Q.law) : P = Q := by
  cases P
  cases Q
  cases h
  rfl

variable {Query Reply Param Out Next H Input : Type}
  [MeasurableSpace Query] [MeasurableSpace Reply] [MeasurableSpace Param]
  [MeasurableSpace Out] [MeasurableSpace Next] [MeasurableSpace H] [MeasurableSpace Input]
  (K : Kernel (Query × H) (Reply × H)) [IsMarkovKernel K]

theorem interpret_pure_law (fallback : Query) (f : Param → Out) (hf : Measurable f) :
    ((pure (Reply := Reply) fallback f hf).interpret K).law =
      (Procedure.pure f hf : Procedure Param H Out).law := by
  ext1 z
  obtain ⟨p,h⟩ := z
  change ((Kernel.id.comap _ _).map _) (p,h) = Measure.dirac (f p,h,0)
  rw [Kernel.map_apply _ (pure fallback f hf).record_measurable, Kernel.comap_apply, Kernel.id_apply,
    Measure.map_dirac (pure fallback f hf).record_measurable]
  rfl

def rawCall (q : Param → Query) (hq : Measurable q) : Procedure Param H Reply where
  law := (K.comap (fun z => (q z.1,z.2)) ((hq.comp measurable_fst).prodMk measurable_snd)).map
    (fun r => (r.1,r.2,1))
  markov := Kernel.IsMarkovKernel.map _ (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))

theorem interpret_call_law (initialReply : Reply) (q : Param → Query) (hq : Measurable q) :
    ((call initialReply q hq).interpret K).law = (rawCall K q hq).law := by
  let P := call initialReply q hq
  have hrecord : Measurable (fun r : Reply × H => (r.1,r.2,(1 : ℕ))) :=
    measurable_fst.prodMk (measurable_snd.prodMk measurable_const)
  ext1 z
  obtain ⟨p,h⟩ := z
  change ((P.interpret K).law (p,h)) = _
  rw [interpret, Kernel.map_apply _ P.record_measurable, Kernel.comap_apply]
  change ((P.execution K 1) ((p,initialReply),h)).map P.record = _
  rw [execution, execution, Kernel.comp_id]
  rw [step, KernelMap.dependent_apply _ _ (P.stepFinish_measurable 0)]
  have hm : Measurable (fun r : Reply × H => P.stepFinish 0 (((p,initialReply),h),r)) :=
    (P.stepFinish_measurable 0).comp (measurable_const.prodMk measurable_id)
  rw [Measure.map_map P.record_measurable hm]
  rw [rawCall, Kernel.map_apply _ hrecord, Kernel.comap_apply]
  rfl

variable (P : Program Query Reply Param Out)

omit [IsMarkovKernel K] in
theorem execution_reparam (f : Input → Param) (hf : Measurable f) (n : ℕ) :
    (P.reparam f hf).execution K n = P.execution K n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [execution]
    rw [ih]
    rfl

omit [IsMarkovKernel K] in
theorem execution_map (f : Out → Next) (hf : Measurable f) (n : ℕ) :
    (P.map f hf).execution K n = P.execution K n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [execution]
    rw [ih]
    rfl

theorem interpret_reparam_law (f : Input → Param) (hf : Measurable f) :
    ((P.reparam f hf).interpret K).law = ((P.interpret K).reparam f hf).law := by
  ext1 z
  rw [Procedure.reparam, Kernel.comap_apply]
  rw [interpret, Kernel.map_apply _ (P.reparam f hf).record_measurable, Kernel.comap_apply]
  rw [interpret, Kernel.map_apply _ P.record_measurable, Kernel.comap_apply, execution_reparam]
  rfl

theorem interpret_map_law (f : Out → Next) (hf : Measurable f) :
    ((P.map f hf).interpret K).law =
      ((P.interpret K).map (fun z => f z.2) (hf.comp measurable_snd)).law := by
  ext1 z
  obtain ⟨p,h⟩ := z
  rw [Procedure.map_law]
  rw [interpret, Kernel.map_apply _ (P.map f hf).record_measurable, Kernel.comap_apply]
  rw [interpret, Kernel.map_apply _ P.record_measurable, Kernel.comap_apply]
  have hm : Measurable (fun z : Outcome Out H => (f z.1,z.2)) :=
    (hf.comp measurable_fst).prodMk measurable_snd
  rw [Measure.map_map hm P.record_measurable]
  rw [execution_map]
  rfl

theorem interpret_pure (fallback : Query) (f : Param → Out) (hf : Measurable f) :
    (pure (Reply := Reply) fallback f hf).interpret K =
      (Procedure.pure f hf : Procedure Param H Out) :=
  procedure_ext _ _ (interpret_pure_law K fallback f hf)

theorem interpret_call (initialReply : Reply) (q : Param → Query) (hq : Measurable q) :
    (call initialReply q hq).interpret K = rawCall K q hq :=
  procedure_ext _ _ (interpret_call_law K initialReply q hq)

theorem interpret_bind (Q : Program Query Reply (Param × Out) Next) :
    (P.bind Q).interpret K = (P.interpret K).bind (Q.interpret K) :=
  procedure_ext _ _ (interpret_bind_law P Q K)

theorem interpret_reparam (f : Input → Param) (hf : Measurable f) :
    (P.reparam f hf).interpret K = (P.interpret K).reparam f hf :=
  procedure_ext _ _ (interpret_reparam_law K P f hf)

theorem interpret_map (f : Out → Next) (hf : Measurable f) :
    (P.map f hf).interpret K = (P.interpret K).map (fun z => f z.2) (hf.comp measurable_snd) :=
  procedure_ext _ _ (interpret_map_law K P f hf)

def mapWithInput (fallback : Query) (f : Param × Out → Next) (hf : Measurable f) :
    Program Query Reply Param Next := P.bind (pure fallback f hf)

theorem interpret_mapWithInput (fallback : Query) (f : Param × Out → Next) (hf : Measurable f) :
    (P.mapWithInput fallback f hf).interpret K = (P.interpret K).map f hf := by
  rw [mapWithInput, interpret_bind, interpret_pure]
  rfl

end Smoothness2601.FixedProgram.Program
