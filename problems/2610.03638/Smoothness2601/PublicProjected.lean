import Smoothness2601.PublicBatches
import Smoothness2601.AdjointKernels
import Smoothness2601.AdjointIteration

/-! Public projected-update and finite-loop instructions, with exact semantic
equalities to the actual conditional kernels used in the adjoint proof. -/
noncomputable section
open MeasureTheory ProbabilityTheory Bilevel.Stateful
namespace Smoothness2601.PublicProjected
open FixedProgram

variable {RawQuery Reply Query Param E : Type}
  [MeasurableSpace RawQuery] [MeasurableSpace Reply] [MeasurableSpace Query] [MeasurableSpace Param]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (C : Program RawQuery Reply Query E) (fallback : RawQuery)

def upperStep (q : Param → Query) (hq : Measurable q) (v : Param → E) (hv : Measurable v)
    (n : ℕ) (α : ℝ) : Program RawQuery Reply (Param × E) E :=
  (PublicBatches.affineBatch C fallback n (-α)).reparam
    (fun z => (q z.1,v z.1-α • z.2))
    ((hq.comp measurable_fst).prodMk ((hv.comp measurable_fst).sub (measurable_snd.const_smul α)))

def rawStep (Z : Program RawQuery Reply Param E) (q : Param → Query) (hq : Measurable q)
    (v : Param → E) (hv : Measurable v) (n : ℕ) (α : ℝ) : Program RawQuery Reply Param E :=
  Z.bind (upperStep C fallback q hq v hv n α)

def projectedStep (Z : Program RawQuery Reply Param E) (q : Param → Query) (hq : Measurable q)
    (v : Param → E) (hv : Measurable v) (V : ℝ) (n : ℕ) (α : ℝ) : Program RawQuery Reply Param E :=
  (rawStep C fallback Z q hq v hv n α).map (Bilevel.Clipping.clip V)
    (AdjointContraction.clip_stronglyMeasurable V measurable_id.stronglyMeasurable).measurable

def run (steps : ℕ → Program RawQuery Reply (Param × E) E) : ℕ → Program RawQuery Reply Param E
  | 0 => Program.pure fallback (fun _ => 0) measurable_const
  | n+1 => (run steps n).bind (steps n)

variable {H Obs : Type} [MeasurableSpace H] [MeasurableSpace Obs]
  (K : Kernel (RawQuery × H) (Reply × H)) [IsMarkovKernel K]
  {σ : ℝ} (O : HistoryOracle (Query := Query) (History := H) (Obs := Obs) (E := E) σ)
  (hcall : C.interpret K = O.call)

include hcall

omit [CompleteSpace E] in
theorem upperStep_interpret (q : Param → Query) (hq : Measurable q) (v : Param → E) (hv : Measurable v)
    (n : ℕ) (α : ℝ) :
    (upperStep C fallback q hq v hv n α).interpret K = AdjointKernels.upperStep O q hq v hv n α := by
  rw [upperStep, Program.interpret_reparam, PublicBatches.affineBatch_interpret C fallback K O hcall]
  rfl

omit [CompleteSpace E] in
theorem rawStep_interpret (Z : Program RawQuery Reply Param E) (q : Param → Query) (hq : Measurable q)
    (v : Param → E) (hv : Measurable v) (n : ℕ) (α : ℝ) :
    (rawStep C fallback Z q hq v hv n α).interpret K =
      AdjointKernels.rawStep O (Z.interpret K) q hq v hv n α := by
  rw [rawStep, Program.interpret_bind, upperStep_interpret C fallback K O hcall]
  rfl

omit [CompleteSpace E] in
theorem projectedStep_interpret (Z : Program RawQuery Reply Param E) (q : Param → Query) (hq : Measurable q)
    (v : Param → E) (hv : Measurable v) (V : ℝ) (n : ℕ) (α : ℝ) :
    (projectedStep C fallback Z q hq v hv V n α).interpret K =
      AdjointKernels.projectedStep O (Z.interpret K) q hq v hv V n α := by
  rw [projectedStep, Program.interpret_map, rawStep_interpret C fallback K O hcall]
  rfl

omit hcall [InnerProductSpace ℝ E] [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem run_interpret (steps : ℕ → Program RawQuery Reply (Param × E) E) (n : ℕ) :
    (run fallback steps n).interpret K = AdjointIteration.run (fun j => (steps j).interpret K) n := by
  induction n with
  | zero => exact Program.interpret_pure K fallback _ _
  | succ n ih =>
    rw [run, Program.interpret_bind, ih]
    rfl

end Smoothness2601.PublicProjected
