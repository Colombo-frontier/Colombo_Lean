import Smoothness2601.PublicSolvers
import Smoothness2601.FixedProgramRandomization
import Smoothness2601.NormalizedExecution


/-! Public normalized outer execution with a private initially sampled uniform
output index. The queries ignore that index; the proved output law is the
same independent uniform path selection used in the stationarity proof. -/
noncomputable section
open MeasureTheory ProbabilityTheory Bilevel.Stateful Bilevel.PrimitiveGeometry
open scoped ENNReal
namespace Smoothness2601.PublicOuter
open FixedProgram NormalizedExecution

variable {X Y : Type}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]

def step (A : Program (Adaptive.Query X Y) (Joint X Y) (X × Y) X) (η : ℝ) (n : ℕ) :
    Program (Adaptive.Query X Y) (Joint X Y) ((X × Y) × Path X n) (Path X (n+1)) :=
  (A.reparam (fun z => (z.2 (Fin.last n),z.1.2))
    (((measurable_pi_apply (Fin.last n)).comp measurable_snd).prodMk
      (measurable_snd.comp measurable_fst))).mapWithInput PublicOracle.fallback
        (NormalizedExecution.append η n) (NormalizedExecution.append_measurable η n)

def path (A : Program (Adaptive.Query X Y) (Joint X Y) (X × Y) X) (η : ℝ) :
    (n : ℕ) → Program (Adaptive.Query X Y) (Joint X Y) (X × Y) (Path X n)
  | 0 => Program.pure PublicOracle.fallback (fun p _ => p.1)
      (measurable_pi_lambda _ (fun _ => measurable_fst))
  | n+1 => (path A η n).bind (step A η n)

def selectInput (n : ℕ) (z : ((X × Y) × Fin n) × Path X n) : X := z.2 z.1.2.castSucc

omit [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [BorelSpace X] [SecondCountableTopology X] [BorelSpace Y] [SecondCountableTopology Y] in
theorem selectInput_measurable (n : ℕ) : Measurable (selectInput (X := X) (Y := Y) n) := by
  have he : Measurable (fun z : Path X n × Fin n => z.1 z.2.castSucc) :=
    measurable_from_prod_countable (fun i => measurable_pi_apply i.castSucc)
  exact he.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))

def selectedProgram (A : Program (Adaptive.Query X Y) (Joint X Y) (X × Y) X) (η : ℝ) (n : ℕ) :
    Program (Adaptive.Query X Y) (Joint X Y) ((X × Y) × Fin n) X :=
  ((path A η n).reparam Prod.fst measurable_fst).mapWithInput PublicOracle.fallback
    (selectInput n) (selectInput_measurable n)

def seedInitial (n : ℕ) [NeZero n] : Kernel (X × Y) ((X × Y) × Fin n) :=
  KernelMap.dependent (Kernel.const (X × Y) (Bilevel.StochasticOuter.uniformLaw n)) id

instance seedInitial_markov (n : ℕ) [NeZero n] : IsMarkovKernel (seedInitial (X := X) (Y := Y) n) :=
  KernelMap.dependent_markov _ _ measurable_id

omit [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [BorelSpace X] [SecondCountableTopology X] [BorelSpace Y] [SecondCountableTopology Y] in
theorem seedInitial_apply (n : ℕ) [NeZero n] (input : X × Y) :
    seedInitial n input = (Bilevel.StochasticOuter.uniformLaw n).map (fun i => (input,i)) := by
  rw [seedInitial, KernelMap.dependent_apply _ _ measurable_id]
  rfl

def algorithm (A : Program (Adaptive.Query X Y) (Joint X Y) (X × Y) X)
    (η : ℝ) (n : ℕ) [NeZero n] : Adaptive.Algorithm X Y :=
  compileRandom (selectedProgram A η n) (seedInitial n)

variable {H : Type} [MeasurableSpace H]
  (K : Kernel (Adaptive.Query X Y × H) (Joint X Y × H)) [IsMarkovKernel K]
  (A : Program (Adaptive.Query X Y) (Joint X Y) (X × Y) X)

omit [CompleteSpace X] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [BorelSpace Y] [SecondCountableTopology Y] in
theorem step_interpret (η : ℝ) (n : ℕ) :
    (step A η n).interpret K = NormalizedExecution.step (A.interpret K) η n := by
  rw [step, Program.interpret_mapWithInput, Program.interpret_reparam]
  rfl

omit [CompleteSpace X] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [BorelSpace Y] [SecondCountableTopology Y] in
theorem path_interpret (η : ℝ) (n : ℕ) :
    (path A η n).interpret K = NormalizedExecution.run (A.interpret K) η n := by
  induction n with
  | zero => exact Program.interpret_pure K PublicOracle.fallback _ _
  | succ n ih =>
    rw [path, Program.interpret_bind, ih, step_interpret]
    rfl

omit [CompleteSpace X] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [BorelSpace Y] [SecondCountableTopology Y] in
theorem selectedProgram_law (η : ℝ) (n : ℕ) (input : X × Y) (i : Fin n) (history : H) :
    ((selectedProgram A η n).interpret K).law ((input,i),history) =
      ((NormalizedExecution.run (A.interpret K) η n).law (input,history)).map
        (fun z => (z.1 i.castSucc,z.2)) := by
  rw [selectedProgram, Program.interpret_mapWithInput, Program.interpret_reparam, path_interpret,
    Procedure.map_law, Procedure.reparam, Kernel.comap_apply]
  rfl

variable {b : Budgets} {P : Population (X := X) (Y := Y) b} (O : Adaptive.Oracle P H)

omit [BorelSpace Y] [SecondCountableTopology Y] in
/-- Initial private uniform randomness is exactly equivalent to independent
uniform selection after the oracle path, since all path queries ignore it. -/
theorem algorithm_output (η : ℝ) (n : ℕ) [NeZero n] (input : X × Y) (history : H) :
    Adaptive.outputKernel (algorithm A η n) O (selectedProgram A η n).horizon history input =
      (NormalizedExecution.outputLaw (A.interpret O.law) η n input history).map
        NormalizedExecution.selected := by
  rw [algorithm, FixedProgram.compileRandom_output]
  apply Measure.ext_of_lintegral
  intro f hf
  have hfr : Measurable (fun z : Outcome X H => f z.1) := hf.comp measurable_fst
  have hattach : Measurable (fun p : (X × Y) × Fin n => (p,history)) :=
    measurable_id.prodMk measurable_const
  have hinner : Measurable (fun s : ((X × Y) × Fin n) × H =>
      ∫⁻ z, f z.1 ∂((selectedProgram A η n).interpret O.law).law s) := hfr.lintegral_kernel
  have hinnerAttach : Measurable (fun p : (X × Y) × Fin n =>
      ∫⁻ z, f z.1 ∂((selectedProgram A η n).interpret O.law).law (p,history)) := hinner.comp hattach
  have hseed : Measurable (fun i : Fin n => (input,i)) := measurable_const.prodMk measurable_id
  rw [Kernel.lintegral_map _ measurable_fst input hf,
    Kernel.lintegral_comp _ _ input hfr,
    Kernel.lintegral_map _ hattach input hinner, seedInitial_apply,
    MeasureTheory.lintegral_map hinnerAttach hseed]
  simp_rw [selectedProgram_law O.law A η n input _ history]
  have hselect (i : Fin n) :
      Measurable (fun z : Outcome (Path X n) H => (z.1 i.castSucc,z.2)) :=
    ((measurable_pi_apply i.castSucc).comp measurable_fst).prodMk measurable_snd
  have hmap (i : Fin n) :
      (∫⁻ z, f z.1 ∂(((NormalizedExecution.run (A.interpret O.law) η n).law (input,history)).map
        (fun z => (z.1 i.castSucc,z.2)))) =
        ∫⁻ z, f (z.1 i.castSucc) ∂(NormalizedExecution.run (A.interpret O.law) η n).law (input,history) :=
    MeasureTheory.lintegral_map hfr (hselect i)
  simp_rw [hmap]
  have hs : Measurable (fun z : Fin n × Outcome (Path X n) H => f (NormalizedExecution.selected z)) :=
    hf.comp (NormalizedExecution.selected_measurable n)
  rw [NormalizedExecution.outputLaw,
    MeasureTheory.lintegral_map hf (NormalizedExecution.selected_measurable n),
    MeasureTheory.lintegral_prod _ hs.aemeasurable]
  rfl


end Smoothness2601.PublicOuter
