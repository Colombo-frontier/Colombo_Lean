import Smoothness2601.FixedProgramPrimitives
import Smoothness2601.InnerOracle

/-! Public original-gradient instructions. All program definitions are made
before a Population or Oracle is introduced. The subsequent equalities prove
that their raw-kernel interpretations are exactly the existing oracle adapters. -/
noncomputable section
open MeasureTheory ProbabilityTheory Bilevel.Stateful Bilevel.PrimitiveGeometry
namespace Smoothness2601.PublicOracle
open FixedProgram

variable {X Y : Type}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]

def fallback : Adaptive.Query X Y := (true,0,0)

def fullCall : Program (Adaptive.Query X Y) (Joint X Y) (Adaptive.Query X Y) (Joint X Y) :=
  Program.call 0 id measurable_id

def blockY (flag : Bool) : Program (Adaptive.Query X Y) (Joint X Y) (X × Y) Y :=
  ((fullCall (X := X) (Y := Y)).reparam (fun q => (flag,q)) (measurable_const.prodMk measurable_id)).map
    (fullSnd (X := X) (Y := Y)) (fullSnd (X := X) (Y := Y)).continuous.measurable

def blockX (flag : Bool) : Program (Adaptive.Query X Y) (Joint X Y) (X × Y) X :=
  ((fullCall (X := X) (Y := Y)).reparam (fun q => (flag,q)) (measurable_const.prodMk measurable_id)).map
    (fullFst (X := X) (Y := Y)) (fullFst (X := X) (Y := Y)).continuous.measurable

variable {b : Budgets} (P : Population (X := X) (Y := Y) b)
  {H : Type} [MeasurableSpace H] (O : Adaptive.Oracle P H)

omit [SecondCountableTopology X] in
theorem fullCall_interpret :
    (fullCall (X := X) (Y := Y)).interpret O.law = (InnerOracle.fullJoint P O).call := by
  rw [fullCall, Program.interpret_call]
  apply Program.procedure_ext
  ext1 z
  obtain ⟨q,h⟩ := z
  have hm : Measurable (fun z : Joint X Y × H => (z.1,z.2,(1:ℕ))) :=
    measurable_fst.prodMk (measurable_snd.prodMk measurable_const)
  rw [Program.rawCall, Kernel.map_apply _ hm, Kernel.comap_apply, HistoryOracle.call_law]
  rfl

theorem blockY_interpret (flag : Bool) :
    (blockY (X := X) (Y := Y) flag).interpret O.law = (InnerOracle.blockY P O flag).call := by
  rw [blockY, Program.interpret_map, Program.interpret_reparam, fullCall_interpret P O]
  apply Program.procedure_ext
  ext1 z
  obtain ⟨q,h⟩ := z
  rw [Procedure.map_law, Procedure.reparam, Kernel.comap_apply, HistoryOracle.call_law,
    HistoryOracle.call_law]
  change ((O.law ((flag,q),h)).map (fun z => (z.1,z.2,(1:ℕ)))).map
      (fun z : Outcome (Joint X Y) H => (z.1.snd,z.2)) =
    (O.law ((flag,q),h)).map (fun z => (z.1.snd,z.2,(1:ℕ)))
  have hm : Measurable (fun z : Outcome (Joint X Y) H => (z.1.snd,z.2)) :=
    ((fullSnd (X := X) (Y := Y)).continuous.measurable.comp measurable_fst).prodMk measurable_snd
  have hr : Measurable (fun z : Joint X Y × H => (z.1,z.2,(1:ℕ))) :=
    measurable_fst.prodMk (measurable_snd.prodMk measurable_const)
  rw [Measure.map_map hm hr]
  rfl

theorem blockX_interpret (flag : Bool) :
    (blockX (X := X) (Y := Y) flag).interpret O.law = (InnerOracle.blockX P O flag).call := by
  rw [blockX, Program.interpret_map, Program.interpret_reparam, fullCall_interpret P O]
  apply Program.procedure_ext
  ext1 z
  obtain ⟨q,h⟩ := z
  rw [Procedure.map_law, Procedure.reparam, Kernel.comap_apply, HistoryOracle.call_law,
    HistoryOracle.call_law]
  change ((O.law ((flag,q),h)).map (fun z => (z.1,z.2,(1:ℕ)))).map
      (fun z : Outcome (Joint X Y) H => (z.1.fst,z.2)) =
    (O.law ((flag,q),h)).map (fun z => (z.1.fst,z.2,(1:ℕ)))
  have hm : Measurable (fun z : Outcome (Joint X Y) H => (z.1.fst,z.2)) :=
    ((fullFst (X := X) (Y := Y)).continuous.measurable.comp measurable_fst).prodMk measurable_snd
  have hr : Measurable (fun z : Joint X Y × H => (z.1,z.2,(1:ℕ))) :=
    measurable_fst.prodMk (measurable_snd.prodMk measurable_const)
  rw [Measure.map_map hm hr]
  rfl

end Smoothness2601.PublicOracle
