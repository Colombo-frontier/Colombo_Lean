import Smoothness2601.FixedProgram

/-! Public random initialization, chosen before any oracle call. In particular
the independent uniform output index can be kept in program state at zero
additional oracle cost. The initializer is independent of Population/Oracle. -/
noncomputable section
open MeasureTheory ProbabilityTheory Bilevel.Stateful Bilevel.PrimitiveGeometry
open scoped ENNReal
namespace Smoothness2601.FixedProgram

variable {X Y Param : Type}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Param]

def compileRandom (P : Program (Adaptive.Query X Y) (Joint X Y) Param X)
    (initial : Kernel (X × Y) Param) [IsMarkovKernel initial] : Adaptive.Algorithm X Y where
  Memory := P.State
  initialLaw := initial.map P.init
  initialMarkov := Kernel.IsMarkovKernel.map _ P.init_measurable
  query := P.query
  query_measurable := P.query_measurable
  update := P.update
  update_measurable := P.update_measurable
  output := P.output
  output_measurable := P.output_measurable

variable {b : Budgets} {population : Population (X := X) (Y := Y) b}
  {H : Type} [MeasurableSpace H]
  (P : Program (Adaptive.Query X Y) (Joint X Y) Param X)
  (initial : Kernel (X × Y) Param) [IsMarkovKernel initial]
  (O : Adaptive.Oracle population H)

theorem compileRandom_execution (n : ℕ) :
    Adaptive.execution (compileRandom P initial) O n = P.execution O.law n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Adaptive.step (compileRandom P initial) O n ∘ₖ
      Adaptive.execution (compileRandom P initial) O n = P.step O.law n ∘ₖ P.execution O.law n
    rw [ih]
    rfl

omit [InnerProductSpace ℝ X] [CompleteSpace X] [InnerProductSpace ℝ Y] [CompleteSpace Y] in
theorem compileRandom_initial (h : H) :
    Adaptive.initialState (compileRandom P initial) h = initial.map (fun p => (P.init p,h)) := by
  change (initial.map P.init).map (fun s : P.State => (s,h)) = _
  exact (Kernel.map_comp_right initial P.init_measurable
    (show Measurable (fun s : P.State => (s,h)) from measurable_id.prodMk measurable_const)).symm

/-- Exact output law for a public program with private initial randomness.
This is a theorem about every initializer and every oracle, not an assumed
algorithm-realizability certificate. -/
theorem compileRandom_output (h : H) :
    Adaptive.outputKernel (compileRandom P initial) O P.horizon h =
      ((P.interpret O.law).law ∘ₖ initial.map (fun p => (p,h))).map Prod.fst := by
  apply Kernel.ext_fun
  intro input f hf
  have hout : Measurable (fun s : P.State × H => P.output s.1) :=
    P.output_measurable.comp measurable_fst
  have hstate : Measurable (fun p : Param => (P.init p,h)) :=
    P.init_measurable.prodMk measurable_const
  have hparam : Measurable (fun p : Param => (p,h)) := measurable_id.prodMk measurable_const
  have hfo : Measurable (fun s : P.State × H => f (P.output s.1)) := hf.comp hout
  have hfr : Measurable (fun z : Outcome X H => f z.1) := hf.comp measurable_fst
  rw [Adaptive.outputKernel]
  erw [Kernel.lintegral_map _ hout input hf]
  erw [Kernel.lintegral_comp _ _ input hfo]
  rw [compileRandom_initial]
  erw [compileRandom_execution]
  have houter : Measurable (fun s : P.State × H =>
      ∫⁻ t, f (P.output t.1) ∂P.execution O.law P.horizon s) := hfo.lintegral_kernel
  erw [Kernel.lintegral_map initial hstate input houter]
  have houter' : Measurable (fun s : Param × H =>
      ∫⁻ z, f z.1 ∂(P.interpret O.law).law s) := hfr.lintegral_kernel
  rw [Kernel.lintegral_map _ measurable_fst input hf,
    Kernel.lintegral_comp _ _ input hfr,
    Kernel.lintegral_map initial hparam input houter']
  apply lintegral_congr
  intro p
  rw [Program.interpret, Kernel.map_apply _ P.record_measurable, Kernel.comap_apply,
    MeasureTheory.lintegral_map hfr P.record_measurable]
  rfl

end Smoothness2601.FixedProgram
