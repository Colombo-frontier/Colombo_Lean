import Smoothness2601.FixedProgramSimulation
import Mathlib.Probability.Kernel.Composition.CompMap

/-! A measurable stopping policy may stop after any number of calls up to N.
Padding it with dummy queries freezes its public memory and preserves its
exact output law, even when the oracle has arbitrary hidden state. -/
noncomputable section
open MeasureTheory ProbabilityTheory Bilevel.Stateful Bilevel.PrimitiveGeometry
namespace Smoothness2601.StoppingPadding

variable {X Y : Type}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y]
  (A : Adaptive.Algorithm X Y) (halt : A.Memory → Bool) (hh : Measurable halt)

/-- After stopping, all original samples are charged but their observations
are ignored. This algorithm uses only public memory and the chosen dummy query. -/
def padded (dummy : Adaptive.Query X Y) : Adaptive.Algorithm X Y where
  Memory := A.Memory
  memoryMeasurable := inferInstance
  initialLaw := A.initialLaw
  initialMarkov := inferInstance
  query k m := if halt m then dummy else A.query k m
  query_measurable k := Measurable.ite (hh (measurableSet_singleton true))
    measurable_const (A.query_measurable k)
  update k z := if halt z.1 then z.1 else A.update k z
  update_measurable k := Measurable.ite ((hh.comp measurable_fst) (measurableSet_singleton true))
    measurable_fst (A.update_measurable k)
  output := A.output
  output_measurable := A.output_measurable

omit [InnerProductSpace ℝ X] [CompleteSpace X] [InnerProductSpace ℝ Y] [CompleteSpace Y] in
theorem padded_never (dummy : Adaptive.Query X Y) :
    padded A (fun _ => false) measurable_const dummy = A := by
  cases A
  rfl

variable {b : Budgets} {P : Population (X := X) (Y := Y) b}
  {H : Type} [MeasurableSpace H] (O : Adaptive.Oracle P H)

def stoppedStep (k : ℕ) : Kernel (A.Memory × H) (A.Memory × H) := by
  classical
  exact Kernel.piecewise ((hh.comp measurable_fst) (measurableSet_singleton true))
    Kernel.id (Adaptive.step A O k)

instance stoppedStep_markov (k : ℕ) : IsMarkovKernel (stoppedStep A halt hh O k) := by
  unfold stoppedStep
  infer_instance

theorem stoppedStep_apply (k : ℕ) (s : A.Memory × H) :
    stoppedStep A halt hh O k s = if halt s.1 then Measure.dirac s else Adaptive.step A O k s := by
  classical
  simp only [stoppedStep,Kernel.piecewise_apply,Kernel.id_apply,Set.mem_preimage,
    Set.mem_singleton_iff,Function.comp_apply]

def stoppedExecution (n : ℕ) : Kernel (A.Memory × H) (A.Memory × H) :=
  FixedProgram.advance (stoppedStep A halt hh O) 0 n

def stoppedOutput (n : ℕ) (history : H) : Kernel (X × Y) X :=
  (stoppedExecution A halt hh O n ∘ₖ Adaptive.initialState A history).map (fun s => A.output s.1)

/-- The state history is irrelevant after stopping. Collapsing it to any one
value provides a genuine kernel simulation for both execution protocols. -/
def collapse (h₀ : H) (s : A.Memory × H) : A.Memory × H :=
  (s.1,if halt s.1 then h₀ else s.2)

omit [InnerProductSpace ℝ X] [CompleteSpace X] [InnerProductSpace ℝ Y] [CompleteSpace Y] in
include hh in
theorem collapse_measurable (h₀ : H) : Measurable (collapse A halt h₀) :=
  measurable_fst.prodMk (Measurable.ite ((hh.comp measurable_fst) (measurableSet_singleton true))
    measurable_const measurable_snd)

omit [InnerProductSpace ℝ X] [CompleteSpace X] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace H] in
theorem collapse_idempotent (h₀ : H) (s : A.Memory × H) :
    collapse A halt h₀ (collapse A halt h₀ s) = collapse A halt h₀ s := by
  simp only [collapse]
  split_ifs <;> rfl

theorem originalStep_law (k : ℕ) (s : A.Memory × H) :
    Adaptive.step A O k s = (O.law (A.query k s.1,s.2)).map
      (fun z => (A.update k (s.1,z.1),z.2)) :=
  KernelMap.dependent_apply _ _ (Adaptive.finishAt_measurable A k) s

theorem paddedStep_active (dummy : Adaptive.Query X Y) (k : ℕ) (s : A.Memory × H)
    (hs : halt s.1 = false) :
    Adaptive.step (padded A halt hh dummy) O k s = Adaptive.step A O k s := by
  rw [originalStep_law,originalStep_law]
  simp only [padded,hs,Bool.false_eq_true,↓reduceIte]

theorem paddedStep_halted (dummy : Adaptive.Query X Y) (k : ℕ) (s : A.Memory × H)
    (h₀ : H) (hs : halt s.1 = true) :
    (Adaptive.step (padded A halt hh dummy) O k s).map (collapse A halt h₀) =
      Measure.dirac (collapse A halt h₀ s) := by
  rw [originalStep_law]
  have hf : Measurable (fun z : Joint X Y × H =>
      ((padded A halt hh dummy).update k (s.1,z.1),z.2)) :=
    (((padded A halt hh dummy).update_measurable k).comp
      (measurable_const.prodMk measurable_fst)).prodMk measurable_snd
  rw [Measure.map_map (collapse_measurable A halt hh h₀) hf]
  have he : (collapse A halt h₀ ∘ fun z : Joint X Y × H =>
      ((padded A halt hh dummy).update k (s.1,z.1),z.2)) = fun _ => collapse A halt h₀ s := by
    funext z
    simp [Function.comp_apply,padded,collapse,hs]
  rw [he,Measure.map_const,measure_univ,one_smul]

def collapsedStep (h₀ : H) (k : ℕ) : Kernel (A.Memory × H) (A.Memory × H) :=
  (stoppedStep A halt hh O k).map (collapse A halt h₀)

theorem collapse_padding_step (dummy : Adaptive.Query X Y) (h₀ : H) (k : ℕ) :
    collapsedStep A halt hh O h₀ k ∘ₖ Kernel.deterministic (collapse A halt h₀)
      (collapse_measurable A halt hh h₀) =
      Kernel.deterministic (collapse A halt h₀) (collapse_measurable A halt hh h₀) ∘ₖ
        Adaptive.step (padded A halt hh dummy) O k := by
  rw [Kernel.comp_deterministic_eq_comap,Kernel.deterministic_comp_eq_map]
  ext1 s
  rw [Kernel.comap_apply,collapsedStep,Kernel.map_apply _ (collapse_measurable A halt hh h₀),
    Kernel.map_apply _ (collapse_measurable A halt hh h₀)]
  cases hs : halt s.1 with
  | false =>
    have he : collapse A halt h₀ s = s := by simp [collapse,hs]
    rw [he,stoppedStep_apply]
    erw [paddedStep_active A halt hh O dummy k s hs]
    simp only [hs,Bool.false_eq_true,↓reduceIte]
  | true =>
    erw [paddedStep_halted A halt hh O dummy k s h₀ hs]
    rw [stoppedStep_apply]
    simp only [collapse,hs,↓reduceIte]
    rw [Measure.map_dirac (collapse_measurable A halt hh h₀)]
    simp [collapse,hs]

theorem collapse_stopped_step (h₀ : H) (k : ℕ) :
    collapsedStep A halt hh O h₀ k ∘ₖ Kernel.deterministic (collapse A halt h₀)
      (collapse_measurable A halt hh h₀) =
      Kernel.deterministic (collapse A halt h₀) (collapse_measurable A halt hh h₀) ∘ₖ
        stoppedStep A halt hh O k := by
  rw [Kernel.comp_deterministic_eq_comap,Kernel.deterministic_comp_eq_map]
  ext1 s
  rw [Kernel.comap_apply,collapsedStep,Kernel.map_apply _ (collapse_measurable A halt hh h₀),
    Kernel.map_apply _ (collapse_measurable A halt hh h₀)]
  cases hs : halt s.1 with
  | false =>
    have he : collapse A halt h₀ s = s := by simp [collapse,hs]
    rw [he]
  | true =>
    rw [stoppedStep_apply,stoppedStep_apply]
    simp only [collapse,hs,↓reduceIte]
    rw [Measure.map_dirac (collapse_measurable A halt hh h₀),
      Measure.map_dirac (collapse_measurable A halt hh h₀)]
    simp [collapse,hs]

theorem execution_eq_advance (dummy : Adaptive.Query X Y) (n : ℕ) :
    Adaptive.execution (padded A halt hh dummy) O n =
      FixedProgram.advance (Adaptive.step (padded A halt hh dummy) O) 0 n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Adaptive.execution,FixedProgram.advance,Nat.zero_add,ih]

set_option maxHeartbeats 1000000 in
theorem output_marginal (dummy : Adaptive.Query X Y) (h₀ : H) (n : ℕ) :
    (Adaptive.execution (padded A halt hh dummy) O n).map (fun s => A.output s.1) =
      (stoppedExecution A halt hh O n).map (fun s => A.output s.1) := by
  have hp := FixedProgram.advance_simulation (Adaptive.step (padded A halt hh dummy) O)
    (collapsedStep A halt hh O h₀) (collapse A halt h₀) (collapse_measurable A halt hh h₀)
    0 0 n (fun j _hj => by simpa only [Nat.zero_add] using collapse_padding_step A halt hh O dummy h₀ j)
  have hs := FixedProgram.advance_simulation (stoppedStep A halt hh O)
    (collapsedStep A halt hh O h₀) (collapse A halt h₀) (collapse_measurable A halt hh h₀)
    0 0 n (fun j _hj => by simpa only [Nat.zero_add] using collapse_stopped_step A halt hh O h₀ j)
  have he := hp.symm.trans hs
  simp only [Kernel.deterministic_comp_eq_map] at he
  have hout : Measurable (fun s : A.Memory × H => A.output s.1) := A.output_measurable.comp measurable_fst
  have hc (K : Kernel (A.Memory × H) (A.Memory × H)) :
      (K.map (collapse A halt h₀)).map (fun s => A.output s.1) = K.map (fun s => A.output s.1) := by
    rw [← Kernel.map_comp_right K (collapse_measurable A halt hh h₀) hout]
    rfl
  have hm := congrArg (fun K => K.map (fun s => A.output s.1)) he
  dsimp only at hm
  erw [hc,hc] at hm
  rw [execution_eq_advance,stoppedExecution]
  exact hm

/-- Exact equality of output measures for every N, initial private random
memory, and valid stateful oracle. Dummy calls can change hidden history but
cannot change the output after stopping. -/
theorem padding_output (dummy : Adaptive.Query X Y) (n : ℕ) (history : H) :
    Adaptive.outputKernel (padded A halt hh dummy) O n history = stoppedOutput A halt hh O n history := by
  change (Adaptive.execution (padded A halt hh dummy) O n ∘ₖ Adaptive.initialState A history).map
      (fun s => A.output s.1) = _
  rw [stoppedOutput,Kernel.map_comp,Kernel.map_comp,output_marginal A halt hh O dummy history n]

omit [InnerProductSpace ℝ X] [CompleteSpace X] [InnerProductSpace ℝ Y] [CompleteSpace Y] in
/-- The stopped process charges at most one call at each of its N positions,
and charges none at positions whose public memory has already stopped. -/
theorem stopped_calls_le (memories : ℕ → A.Memory) (N : ℕ) :
    (∑ k ∈ Finset.range N, if halt (memories k) then (0:ℕ) else 1) ≤ N := by
  calc
    _ ≤ ∑ _k ∈ Finset.range N, (1:ℕ) := Finset.sum_le_sum (fun k _ => by split_ifs <;> omega)
    _ = N := by simp

end Smoothness2601.StoppingPadding
