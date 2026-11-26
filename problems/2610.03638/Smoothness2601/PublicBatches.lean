import Smoothness2601.FixedProgramPrimitives
import Smoothness2601.InnerSolve
import Smoothness2601.SequentialBatches

/-! Public program constructors mirroring the actual batch/inner kernels.
The operational definitions have no Population, Oracle or hidden-history
argument. Semantic proofs compose the already proved primitive call equality. -/
noncomputable section
open MeasureTheory ProbabilityTheory Bilevel.Stateful
namespace Smoothness2601.PublicBatches
open FixedProgram

variable {RawQuery Reply Query Param E : Type}
  [MeasurableSpace RawQuery] [MeasurableSpace Reply] [MeasurableSpace Query] [MeasurableSpace Param]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (C : Program RawQuery Reply Query E) (fallback : RawQuery)

def oracleStep (q : Param → Query) (hq : Measurable q) (d : Param → E)
    (hd : Measurable d) (η : Param → ℝ) (hη : Measurable η) : Program RawQuery Reply Param E :=
  (C.reparam q hq).mapWithInput fallback (fun z => d z.1-η z.1 • z.2)
    ((hd.comp measurable_fst).sub ((hη.comp measurable_fst).smul measurable_snd))

def sum : ℕ → Program RawQuery Reply Query E
  | 0 => Program.pure fallback (fun _ => 0) measurable_const
  | n+1 => (sum n).bind
      (oracleStep C fallback Prod.fst measurable_fst Prod.snd measurable_snd
        (fun _ => -1) measurable_const)

def affineBatch (n : ℕ) (α : ℝ) : Program RawQuery Reply (Query × E) E :=
  ((sum C fallback n).reparam Prod.fst measurable_fst).mapWithInput fallback
    (fun z => z.1.2-(α/(n:ℝ)) • z.2) (by fun_prop)

def innerStep (q : Param × E → Query) (hq : Measurable q) (n : ℕ) (α : ℝ) :
    Program RawQuery Reply (Param × E) E :=
  (affineBatch C fallback n α).reparam (fun z => (q z,z.2)) (hq.prodMk measurable_snd)

def innerIterate (q : Param × E → Query) (hq : Measurable q)
    (initial : Param → E) (hi : Measurable initial) (α : ℝ) (B : ℕ → ℕ) :
    ℕ → Program RawQuery Reply Param E
  | 0 => Program.pure fallback initial hi
  | k+1 => (innerIterate q hq initial hi α B k).bind (innerStep C fallback q hq (B k) α)

def nodeStep (q : ℕ → Param → Query) (hq : ∀ j, Measurable (q j))
    (d : ℕ → ℝ) (batch : ℕ → ℕ) (j : ℕ) : Program RawQuery Reply (Param × E) E :=
  (affineBatch C fallback (batch j) (-d j)).reparam
    (fun z => (q j z.1,z.2)) ((hq j).comp measurable_fst |>.prodMk measurable_snd)

def sequentialRun (q : ℕ → Param → Query) (hq : ∀ j, Measurable (q j))
    (d : ℕ → ℝ) (batch : ℕ → ℕ) : ℕ → Program RawQuery Reply Param E
  | 0 => Program.pure fallback (fun _ => 0) measurable_const
  | n+1 => (sequentialRun q hq d batch n).bind (nodeStep C fallback q hq d batch n)

variable {History Obs : Type} [MeasurableSpace History] [MeasurableSpace Obs]
  (K : Kernel (RawQuery × History) (Reply × History)) [IsMarkovKernel K]
  {σ : ℝ} (O : HistoryOracle (Query := Query) (History := History) (Obs := Obs) (E := E) σ)
  (hcall : C.interpret K = O.call)

include hcall

omit [CompleteSpace E] in
theorem oracleStep_interpret (q : Param → Query) (hq : Measurable q) (d : Param → E)
    (hd : Measurable d) (η : Param → ℝ) (hη : Measurable η) :
    (oracleStep C fallback q hq d hd η hη).interpret K = O.step q hq d hd η hη := by
  rw [oracleStep, Program.interpret_mapWithInput, Program.interpret_reparam, hcall]
  rfl

omit [CompleteSpace E] in
theorem sum_interpret (n : ℕ) : (sum C fallback n).interpret K = O.sum n := by
  induction n with
  | zero => exact Program.interpret_pure K fallback _ _
  | succ n ih =>
    rw [sum, Program.interpret_bind, ih, oracleStep_interpret C fallback K O hcall]
    rfl

omit [CompleteSpace E] in
theorem affineBatch_interpret (n : ℕ) (α : ℝ) :
    (affineBatch C fallback n α).interpret K = InnerBatch.affineBatch O n α := by
  rw [affineBatch, Program.interpret_mapWithInput, Program.interpret_reparam, sum_interpret C fallback K O hcall]
  rfl

omit [CompleteSpace E] in
theorem innerStep_interpret (q : Param × E → Query) (hq : Measurable q) (n : ℕ) (α : ℝ) :
    (innerStep C fallback q hq n α).interpret K = InnerSolve.batchedStep O q hq n α := by
  rw [innerStep, Program.interpret_reparam, affineBatch_interpret C fallback K O hcall]
  rfl

omit [CompleteSpace E] in
theorem innerIterate_interpret (q : Param × E → Query) (hq : Measurable q)
    (initial : Param → E) (hi : Measurable initial) (α : ℝ) (B : ℕ → ℕ) (n : ℕ) :
    (innerIterate C fallback q hq initial hi α B n).interpret K =
      InnerSolve.iterate O q hq initial hi α B n := by
  induction n with
  | zero => exact Program.interpret_pure K fallback _ _
  | succ n ih =>
    rw [innerIterate, Program.interpret_bind, ih, innerStep_interpret C fallback K O hcall]
    rfl

omit [CompleteSpace E] in
theorem nodeStep_interpret (q : ℕ → Param → Query) (hq : ∀ j, Measurable (q j))
    (d : ℕ → ℝ) (batch : ℕ → ℕ) (j : ℕ) :
    (nodeStep C fallback q hq d batch j).interpret K = SequentialBatches.nodeStep O q hq d batch j := by
  rw [nodeStep, Program.interpret_reparam, affineBatch_interpret C fallback K O hcall]
  rfl

omit [CompleteSpace E] in
theorem sequentialRun_interpret (q : ℕ → Param → Query) (hq : ∀ j, Measurable (q j))
    (d : ℕ → ℝ) (batch : ℕ → ℕ) (n : ℕ) :
    (sequentialRun C fallback q hq d batch n).interpret K = SequentialBatches.run O q hq d batch n := by
  induction n with
  | zero => exact Program.interpret_pure K fallback _ _
  | succ n ih =>
    rw [sequentialRun, Program.interpret_bind, ih, nodeStep_interpret C fallback K O hcall]
    rfl

end Smoothness2601.PublicBatches
