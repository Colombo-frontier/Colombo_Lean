import Smoothness2601.AdaptiveModel
import Bilevel.IndependentDraws

/-! Exact law of a fresh-seed oracle execution, including arbitrary private
initial randomization. This connects pathwise lower-bound couplings to the
kernel-based minimax model without imposing any restriction on queries. -/
noncomputable section
open MeasureTheory ProbabilityTheory Bilevel.PrimitiveGeometry
open Bilevel.Stateful Bilevel.IndependentDraws
open scoped ENNReal
namespace Smoothness2601.IndependentExecution

variable {X Y : Type}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  {Seed : Type} [MeasurableSpace Seed]
  (A : Adaptive.Algorithm X Y)
  (sample : Adaptive.Query X Y → Seed → Joint X Y)
  (hs : Measurable (fun z : Adaptive.Query X Y × Seed => sample z.1 z.2))

def memoryRun (m : A.Memory) (n : ℕ) (z : Draws Seed n) : A.Memory :=
  run A.query (fun k s g => A.update k (s,g)) sample m n z

include hs
omit [InnerProductSpace ℝ X] [CompleteSpace X] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [BorelSpace X] [SecondCountableTopology X] [BorelSpace Y] [SecondCountableTopology Y] in
theorem memoryRun_measurable (m : A.Memory) (n : ℕ) : Measurable (memoryRun A sample m n) :=
  run_measurable A.query _ sample m A.query_measurable A.update_measurable hs n

omit [InnerProductSpace ℝ X] [CompleteSpace X] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [BorelSpace X] [SecondCountableTopology X] [BorelSpace Y] [SecondCountableTopology Y] in
theorem memoryRun_joint_measurable (n : ℕ) :
    Measurable (fun z : A.Memory × Draws Seed n => memoryRun A sample z.1 n z.2) := by
  induction n with
  | zero => exact measurable_fst
  | succ n ih =>
    have hstate : Measurable (fun z : A.Memory × (Draws Seed n × Seed) =>
        memoryRun A sample z.1 n z.2.1) :=
      ih.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
    exact (A.update_measurable n).comp (hstate.prodMk
      (hs.comp (((A.query_measurable n).comp hstate).prodMk (measurable_snd.comp measurable_snd))))

variable {b : Budgets} {P : Population (X := X) (Y := Y) b}
  (O : Adaptive.Oracle P Unit) (ν : Measure Seed) [IsProbabilityMeasure ν]
  (hlaw : ∀ q, O.law (q,()) = ν.map (fun seed => (sample q seed,())))

include hlaw
omit [BorelSpace X] [SecondCountableTopology X] [BorelSpace Y] [SecondCountableTopology Y]
  [IsProbabilityMeasure ν] in
theorem step_law (k : ℕ) (m : A.Memory) :
    Adaptive.step A O k (m,()) = ν.map (fun seed => (A.update k (m,sample (A.query k m) seed),())) := by
  rw [Adaptive.step, KernelMap.dependent_apply _ _ (Adaptive.finishAt_measurable A k),
    Kernel.comap_apply, Adaptive.inputAt, hlaw]
  have hsample : Measurable (fun seed => (sample (A.query k m) seed,())) :=
    (hs.comp (measurable_const.prodMk measurable_id)).prodMk measurable_const
  have hfinish : Measurable (fun z : Joint X Y × Unit => Adaptive.finishAt A k ((m,()),z)) :=
    (Adaptive.finishAt_measurable A k).comp (measurable_const.prodMk measurable_id)
  rw [Measure.map_map hfinish hsample]
  rfl

include hs hlaw in
omit [BorelSpace X] [SecondCountableTopology X] [BorelSpace Y] [SecondCountableTopology Y] in
theorem execution_law (n : ℕ) (m : A.Memory) :
    Adaptive.execution A O n (m,()) =
      (law ν n).map (fun z => (memoryRun A sample m n z,())) := by
  induction n with
  | zero =>
    simp only [Adaptive.execution, Kernel.id_apply, law, memoryRun, run,
      Measure.map_const, measure_univ, one_smul]
  | succ n ih =>
    apply Measure.ext_of_lintegral
    intro f hf
    have hinner : Measurable (fun s : A.Memory × Unit => ∫⁻ t, f t ∂Adaptive.step A O n s) :=
      hf.lintegral_kernel
    have hstate : Measurable (fun z : Draws Seed n => (memoryRun A sample m n z,())) :=
      (memoryRun_measurable A sample hs m n).prodMk measurable_const
    rw [Adaptive.execution, Kernel.lintegral_comp _ _ (m,()) hf, ih,
      MeasureTheory.lintegral_map hinner hstate]
    simp_rw [step_law A sample hs O ν hlaw]
    have hnext (state : A.Memory) : Measurable
        (fun seed => (A.update n (state,sample (A.query n state) seed),())) :=
      ((A.update_measurable n).comp (measurable_const.prodMk
        (hs.comp (measurable_const.prodMk measurable_id)))).prodMk measurable_const
    simp_rw [MeasureTheory.lintegral_map hf (hnext _)]
    have hfull : Measurable (fun z : Draws Seed (n+1) => (memoryRun A sample m (n+1) z,())) :=
      (memoryRun_measurable A sample hs m (n+1)).prodMk measurable_const
    have hi : Measurable (fun z : Draws Seed n × Seed => f (memoryRun A sample m (n+1) z,())) :=
      hf.comp hfull
    rw [MeasureTheory.lintegral_map hf hfull, law]
    erw [MeasureTheory.lintegral_prod _ hi.aemeasurable]
    rfl

include hs hlaw in
omit [BorelSpace X] [SecondCountableTopology X] [BorelSpace Y] [SecondCountableTopology Y] in
/-- Arbitrary private random memory remains independent of every fresh oracle
seed. The equality includes unrestricted measurable final outputs. -/
theorem output_law (n : ℕ) (input : X × Y) :
    Adaptive.outputKernel A O n () input =
      ((A.initialLaw input).prod (law ν n)).map
        (fun z => A.output (memoryRun A sample z.1 n z.2)) := by
  apply Measure.ext_of_lintegral
  intro f hf
  have hout : Measurable (fun s : A.Memory × Unit => A.output s.1) :=
    A.output_measurable.comp measurable_fst
  have hfo : Measurable (fun s : A.Memory × Unit => f (A.output s.1)) := hf.comp hout
  rw [Adaptive.outputKernel, Kernel.lintegral_map _ hout input hf,
    Kernel.lintegral_comp _ _ input hfo, Adaptive.initialState]
  have hinner : Measurable (fun s : A.Memory × Unit =>
      ∫⁻ t, f (A.output t.1) ∂Adaptive.execution A O n s) := hfo.lintegral_kernel
  have hattach : Measurable (fun m : A.Memory => (m,())) := measurable_id.prodMk measurable_const
  rw [Kernel.lintegral_map A.initialLaw hattach input hinner]
  simp_rw [execution_law A sample hs O ν hlaw]
  have hstate (m : A.Memory) : Measurable (fun z : Draws Seed n => (memoryRun A sample m n z,())) :=
    (memoryRun_measurable A sample hs m n).prodMk measurable_const
  simp_rw [MeasureTheory.lintegral_map hfo (hstate _)]
  have hall : Measurable (fun z : A.Memory × Draws Seed n => A.output (memoryRun A sample z.1 n z.2)) :=
    A.output_measurable.comp (memoryRun_joint_measurable A sample hs n)
  have hi : Measurable (fun z : A.Memory × Draws Seed n => f (A.output (memoryRun A sample z.1 n z.2))) :=
    hf.comp hall
  rw [MeasureTheory.lintegral_map hf hall, MeasureTheory.lintegral_prod _ hi.aemeasurable]

end Smoothness2601.IndependentExecution
