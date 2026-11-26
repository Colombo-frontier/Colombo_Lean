import Smoothness2601.FixedProgramSimulation

/-! The state-machine bind has exactly the same conditional law as binding
the interpreted component procedures. No population-dependent realizability
certificate is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Bilevel.Stateful
open scoped ENNReal
namespace Smoothness2601.FixedProgram.Program

variable {Query Reply Param Out Next H : Type}
  [MeasurableSpace Query] [MeasurableSpace Reply] [MeasurableSpace Param]
  [MeasurableSpace Out] [MeasurableSpace Next] [MeasurableSpace H]
  (P : Program Query Reply Param Out) (Q : Program Query Reply (Param × Out) Next)
  (K : Kernel (Query × H) (Reply × H)) [IsMarkovKernel K]

def firstEmbedding (p : Param) (s : P.State) : (P.bind Q).State :=
  (p,s,Q.init (p,P.output s))

theorem firstEmbedding_measurable (p : Param) : Measurable (firstEmbedding P Q p) :=
  measurable_const.prodMk (measurable_id.prodMk
    (Q.init_measurable.comp (measurable_const.prodMk P.output_measurable)))

def secondEmbedding (p : Param) (s : P.State) (t : Q.State) : (P.bind Q).State := (p,s,t)

theorem secondEmbedding_measurable (p : Param) (s : P.State) :
    Measurable (secondEmbedding P Q p s) :=
  measurable_const.prodMk (measurable_const.prodMk measurable_id)

theorem first_stage (p : Param) (s : P.State) (h : H) :
    advance ((P.bind Q).step K) 0 P.horizon (firstEmbedding P Q p s,h) =
      (advance (P.step K) 0 P.horizon (s,h)).map (historyMap (firstEmbedding P Q p)) := by
  apply execution_simulation_apply P (P.bind Q) K _ (firstEmbedding_measurable P Q p) 0 0 P.horizon
  · intro j hj s
    simp only [Nat.zero_add, bind, firstEmbedding, if_pos hj]
  · intro j hj s r
    simp only [Nat.zero_add, bind, firstEmbedding, if_pos hj]

theorem second_stage (p : Param) (s : P.State) (t : Q.State) (h : H) :
    advance ((P.bind Q).step K) P.horizon Q.horizon (secondEmbedding P Q p s t,h) =
      (advance (Q.step K) 0 Q.horizon (t,h)).map (historyMap (secondEmbedding P Q p s)) := by
  apply execution_simulation_apply Q (P.bind Q) K _ (secondEmbedding_measurable P Q p s)
    0 P.horizon Q.horizon
  · intro j _ t
    simp only [Nat.zero_add, bind, secondEmbedding,
      if_neg (show ¬P.horizon+j < P.horizon by omega), Nat.add_sub_cancel_left]
  · intro j _ t r
    simp only [Nat.zero_add, bind, secondEmbedding,
      if_neg (show ¬P.horizon+j < P.horizon by omega), Nat.add_sub_cancel_left]

theorem lintegral_interpret (p : Param) (h : H) (f : Outcome Out H → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, f z ∂(P.interpret K).law (p,h)) =
      ∫⁻ s, f (P.record s) ∂advance (P.step K) 0 P.horizon (P.init p,h) := by
  rw [interpret, Kernel.map_apply _ P.record_measurable, Kernel.comap_apply,
    MeasureTheory.lintegral_map hf P.record_measurable, execution_eq_advance]
  rfl

def totalRecord (s : Q.State × H) : Outcome Next H :=
  (Q.output s.1,s.2,P.horizon+Q.horizon)

theorem totalRecord_measurable : Measurable (totalRecord P Q (H := H)) :=
  (Q.output_measurable.comp measurable_fst).prodMk (measurable_snd.prodMk measurable_const)

theorem second_stage_lintegral (p : Param) (s : P.State × H)
    (f : Outcome Next H → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ t, f ((P.bind Q).record t)
      ∂advance ((P.bind Q).step K) P.horizon Q.horizon
        (historyMap (firstEmbedding P Q p) s)) =
      ∫⁻ t, f (totalRecord P Q t)
        ∂advance (Q.step K) 0 Q.horizon (Q.init (p,P.output s.1),s.2) := by
  have he := second_stage P Q K p s.1 (Q.init (p,P.output s.1)) s.2
  change advance ((P.bind Q).step K) P.horizon Q.horizon
      (historyMap (firstEmbedding P Q p) s) = _ at he
  have hfr : Measurable (fun t : (P.bind Q).State × H => f ((P.bind Q).record t)) :=
    hf.comp (P.bind Q).record_measurable
  rw [he, MeasureTheory.lintegral_map hfr
    (historyMap_measurable (secondEmbedding_measurable P Q p s.1))]
  rfl

theorem lintegral_interpret_bind (p : Param) (h : H)
    (f : Outcome Next H → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, f z ∂((P.bind Q).interpret K).law (p,h)) =
      ∫⁻ s, ∫⁻ t, f (totalRecord P Q t)
        ∂advance (Q.step K) 0 Q.horizon (Q.init (p,P.output s.1),s.2)
          ∂advance (P.step K) 0 P.horizon (P.init p,h) := by
  rw [lintegral_interpret (P.bind Q) K p h f hf,
    show (P.bind Q).horizon = P.horizon+Q.horizon from rfl,
    advance_add, Nat.zero_add]
  have hfr : Measurable (fun t : (P.bind Q).State × H => f ((P.bind Q).record t)) :=
    hf.comp (P.bind Q).record_measurable
  rw [Kernel.lintegral_comp _ _ _ hfr]
  change (∫⁻ s, (∫⁻ t, f ((P.bind Q).record t)
    ∂advance ((P.bind Q).step K) P.horizon Q.horizon s)
    ∂advance ((P.bind Q).step K) 0 P.horizon (firstEmbedding P Q p (P.init p),h)) = _
  rw [first_stage]
  rw [MeasureTheory.lintegral_map
    (hfr.lintegral_kernel)
    (historyMap_measurable (firstEmbedding_measurable P Q p))]
  simp_rw [second_stage_lintegral P Q K p _ f hf]

theorem interpret_bind_law :
    ((P.bind Q).interpret K).law = ((P.interpret K).bind (Q.interpret K)).law := by
  apply Kernel.ext_fun
  intro input f hf
  obtain ⟨p,h⟩ := input
  have hfc : Measurable (fun z : Outcome Out H × Outcome Next H => f (Procedure.combine z)) :=
    hf.comp Procedure.combine_measurable
  rw [lintegral_interpret_bind P Q K p h f hf, Procedure.bind_law_eq,
    MeasureTheory.lintegral_map hf Procedure.combine_measurable,
    Measure.lintegral_compProd hfc]
  rw [lintegral_interpret P K p h]
  · apply lintegral_congr
    intro s
    change (∫⁻ t, f (totalRecord P Q t)
      ∂advance (Q.step K) 0 Q.horizon (Q.init (p,P.output s.1),s.2)) =
      ∫⁻ w, f (Procedure.combine (P.record s,w))
        ∂(Q.interpret K).law ((p,(P.record s).1),(P.record s).2.1)
    have hff : Measurable (fun w : Outcome Next H => f (Procedure.combine (P.record s,w))) :=
      hfc.comp (measurable_const.prodMk measurable_id)
    rw [lintegral_interpret Q K _ _ _ hff]
    rfl
  · exact hfc.lintegral_kernel_prod_right'

end Smoothness2601.FixedProgram.Program
