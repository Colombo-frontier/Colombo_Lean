import HeavyTail.AdaptiveKernelRandomized
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Tactic.Tauto

/-! Bounded causal stopping. The live law is restricted to paths which continue
BEFORE the next composition-product, so stopped paths make no further calls.
The stopped output law sums the exit laws and the mandatory terminal output.
Padding preserves this output law by a proved measure identity. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators
namespace HeavyTail.AdaptiveKernel
universe u v w

section MeasureLemmas
variable {H R Y : Type*} [MeasurableSpace H] [MeasurableSpace R] [MeasurableSpace Y]

theorem compProd_restrict_past (μ : Measure H) [IsFiniteMeasure μ]
    (K : Kernel H R) [IsMarkovKernel K] (S : Set H) (hS : MeasurableSet S) :
    (μ.restrict S).compProd K = (μ.compProd K).restrict (Prod.fst ⁻¹' S) := by
  ext C hC
  rw [Measure.compProd_apply hC, Measure.restrict_apply hC,
    Measure.compProd_apply (hC.inter (hS.preimage measurable_fst)),
    ← lintegral_indicator hS]
  apply lintegral_congr
  intro h
  by_cases hh : h ∈ S
  · simp only [Set.indicator_of_mem hh]
    congr 1
    ext r
    simp [hh]
  · simp only [Set.indicator_of_not_mem hh]
    have hempty : Prod.mk h ⁻¹' (C ∩ Prod.fst ⁻¹' S) = ∅ := by ext r; simp [hh]
    rw [hempty, measure_empty]

theorem compProd_map_past (μ : Measure H) [IsFiniteMeasure μ]
    (K : Kernel H R) [IsMarkovKernel K] (f : H → Y) (hf : Measurable f) :
    (μ.compProd K).map (fun z => f z.1) = μ.map f := by
  calc
    _ = ((μ.compProd K).map Prod.fst).map f :=
      (Measure.map_map (μ := μ.compProd K) hf (measurable_fst : Measurable (Prod.fst : H × R → H))).symm
    _ = μ.map f := congrArg (fun ν => ν.map f) (Measure.fst_compProd μ K)

theorem compProd_restrict_map_past (μ : Measure H) [IsFiniteMeasure μ]
    (K : Kernel H R) [IsMarkovKernel K] (S : Set H) (hS : MeasurableSet S)
    (g : H × R → Y) (f : H → Y) (hf : Measurable f)
    (hgf : ∀ h ∈ S, ∀ r, g (h, r) = f h) :
    ((μ.restrict S).compProd K).map g = (μ.restrict S).map f := by
  calc
    _ = ((μ.restrict S).compProd K).map (fun z => f z.1) := by
      apply Measure.map_congr
      rw [compProd_restrict_past μ K S hS]
      filter_upwards [ae_restrict_mem (hS.preimage measurable_fst)] with z hz
      exact hgf z.1 hz z.2
    _ = _ := compProd_map_past _ K f hf

end MeasureLemmas

structure StoppingRule (Seed Reply : Type u) (Output : Type w)
    [MeasurableSpace Seed] [MeasurableSpace Reply] [MeasurableSpace Output] where
  halt : (n : ℕ) → Set (History Seed Reply n)
  halt_measurable : ∀ n, MeasurableSet (halt n)
  value : (n : ℕ) → History Seed Reply n → Output
  value_measurable : ∀ n, Measurable (value n)

namespace StoppingRule
variable {Seed Reply : Type u} {Query : Type v} {Output : Type w}
  [MeasurableSpace Seed] [MeasurableSpace Reply] [MeasurableSpace Query]
  [MeasurableSpace Output] {T : ℕ}

/-- Histories that have not halted strictly before the current time. -/
def survival (S : StoppingRule Seed Reply Output) : (n : ℕ) → Set (History Seed Reply n)
  | 0 => Set.univ
  | n + 1 => Prod.fst ⁻¹' (S.survival n ∩ (S.halt n)ᶜ)

theorem survival_measurable (S : StoppingRule Seed Reply Output) (n : ℕ) :
    MeasurableSet (S.survival n) := by
  induction n with
  | zero => exact MeasurableSet.univ
  | succ n ih => exact (ih.inter (S.halt_measurable n).compl).preimage measurable_fst

/-- Once halted, the recorded output is frozen; otherwise it is the current
terminal output. This is a measurable function of the observed prefix. -/
def carriedValue (S : StoppingRule Seed Reply Output) :
    (n : ℕ) → History Seed Reply n → Output
  | 0 => S.value 0
  | n + 1 => fun h => if h.1 ∈ S.survival n then
      if h.1 ∈ S.halt n then S.value n h.1 else S.value (n + 1) h
    else S.carriedValue n h.1

theorem carriedValue_measurable (S : StoppingRule Seed Reply Output) (n : ℕ) :
    Measurable (S.carriedValue n) := by
  induction n with
  | zero => exact S.value_measurable 0
  | succ n ih =>
    exact Measurable.ite ((S.survival_measurable n).preimage measurable_fst)
      (Measurable.ite ((S.halt_measurable n).preimage measurable_fst)
        ((S.value_measurable n).comp measurable_fst) (S.value_measurable (n + 1)))
      (ih.comp measurable_fst)

theorem carriedValue_of_survival (S : StoppingRule Seed Reply Output)
    (n : ℕ) (h : History Seed Reply n) (hh : h ∈ S.survival n) :
    S.carriedValue n h = S.value n h := by
  cases n with
  | zero => rfl
  | succ n =>
    change h.1 ∈ S.survival n ∧ h.1 ∉ S.halt n at hh
    simp only [carriedValue, if_pos hh.1, if_neg hh.2]

def paddedPolicy (S : StoppingRule Seed Reply Output) (A : Policy Seed Query Reply Output T) :
    Policy Seed Query Reply Output T where
  query := A.query
  query_measurable := A.query_measurable
  output := S.carriedValue T
  output_measurable := S.carriedValue_measurable T

theorem paddedPolicy_historyLaw (S : StoppingRule Seed Reply Output)
    (A : Policy Seed Query Reply Output T) (μ : Measure Seed) (K : Kernel Query Reply) (n : ℕ) :
    (S.paddedPolicy A).historyLaw μ K n = A.historyLaw μ K n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Policy.historyLaw_succ, ih]; rfl

def liveLaw (S : StoppingRule Seed Reply Output) (A : Policy Seed Query Reply Output T)
    (μ : Measure Seed) (K : Kernel Query Reply) : (n : ℕ) → Measure (History Seed Reply n)
  | 0 => μ
  | n + 1 => ((S.liveLaw A μ K n).restrict (S.halt n)ᶜ).compProd (A.replyKernel K n)

instance liveLaw_finite (S : StoppingRule Seed Reply Output)
    (A : Policy Seed Query Reply Output T) (μ : Measure Seed) [IsFiniteMeasure μ]
    (K : Kernel Query Reply) [IsMarkovKernel K] (n : ℕ) : IsFiniteMeasure (S.liveLaw A μ K n) := by
  induction n with
  | zero => exact inferInstanceAs (IsFiniteMeasure μ)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (IsFiniteMeasure
      (((S.liveLaw A μ K n).restrict (S.halt n)ᶜ).compProd (A.replyKernel K n)))

def exitedLaw (S : StoppingRule Seed Reply Output) (A : Policy Seed Query Reply Output T)
    (μ : Measure Seed) (K : Kernel Query Reply) : ℕ → Measure Output
  | 0 => 0
  | n + 1 => S.exitedLaw A μ K n + ((S.liveLaw A μ K n).restrict (S.halt n)).map (S.value n)

/-- The actual stopped algorithm outputs at its first halt before T, or at T.
Only live paths enter a fresh raw-response composition-product. -/
def outputLaw (S : StoppingRule Seed Reply Output) (A : Policy Seed Query Reply Output T)
    (μ : Measure Seed) (K : Kernel Query Reply) : Measure Output :=
  S.exitedLaw A μ K T + (S.liveLaw A μ K T).map (S.value T)

theorem liveLaw_eq_restrict (S : StoppingRule Seed Reply Output)
    (A : Policy Seed Query Reply Output T) (μ : Measure Seed) [IsProbabilityMeasure μ]
    (K : Kernel Query Reply) [IsMarkovKernel K] (n : ℕ) :
    S.liveLaw A μ K n = (A.historyLaw μ K n).restrict (S.survival n) := by
  induction n with
  | zero => simp only [liveLaw, Policy.historyLaw_zero, survival, Measure.restrict_univ]
  | succ n ih =>
    rw [liveLaw, ih, Measure.restrict_restrict (S.halt_measurable n).compl]
    rw [compProd_restrict_past (A.historyLaw μ K n) (A.replyKernel K n) _
      ((S.halt_measurable n).compl.inter (S.survival_measurable n))]
    change (A.historyLaw μ K (n + 1)).restrict
      (Prod.fst ⁻¹' ((S.halt n)ᶜ ∩ S.survival n)) = _
    rw [Set.inter_comm]
    rfl

theorem exitedLaw_eq_restrict (S : StoppingRule Seed Reply Output)
    (A : Policy Seed Query Reply Output T) (μ : Measure Seed) [IsProbabilityMeasure μ]
    (K : Kernel Query Reply) [IsMarkovKernel K] (n : ℕ) :
    S.exitedLaw A μ K n =
      ((A.historyLaw μ K n).restrict (S.survival n)ᶜ).map (S.carriedValue n) := by
  induction n with
  | zero => simp only [exitedLaw, survival, compl_univ, Measure.restrict_empty, Measure.map_zero]
  | succ n ih =>
    have hparts : (S.survival (n + 1))ᶜ =
        Prod.fst ⁻¹' (S.survival n)ᶜ ∪ Prod.fst ⁻¹' (S.survival n ∩ S.halt n) := by
      ext h
      simp only [survival, mem_compl_iff, mem_preimage, mem_inter_iff, mem_union]
      tauto
    have hdisj : Disjoint ((Prod.fst : History Seed Reply (n + 1) → History Seed Reply n) ⁻¹' (S.survival n)ᶜ)
        (Prod.fst ⁻¹' (S.survival n ∩ S.halt n)) := by
      apply Set.disjoint_left.mpr
      intro h hleft hright
      exact hleft hright.1
    rw [exitedLaw, ih, liveLaw_eq_restrict, Measure.restrict_restrict (S.halt_measurable n)]
    rw [hparts, Measure.restrict_union hdisj
      (((S.survival_measurable n).inter (S.halt_measurable n)).preimage measurable_fst),
      Measure.map_add _ _ (S.carriedValue_measurable (n + 1))]
    simp only [Policy.historyLaw_succ]
    rw [← compProd_restrict_past (A.historyLaw μ K n) (A.replyKernel K n) _ (S.survival_measurable n).compl,
      ← compProd_restrict_past (A.historyLaw μ K n) (A.replyKernel K n) _
        ((S.survival_measurable n).inter (S.halt_measurable n))]
    rw [compProd_restrict_map_past (A.historyLaw μ K n) (A.replyKernel K n) _ (S.survival_measurable n).compl
      (S.carriedValue (n + 1)) (S.carriedValue n) (S.carriedValue_measurable n)
      (by intro h hh r; simp only [carriedValue, if_neg hh])]
    rw [compProd_restrict_map_past (A.historyLaw μ K n) (A.replyKernel K n) _
      ((S.survival_measurable n).inter (S.halt_measurable n))
      (S.carriedValue (n + 1)) (S.value n) (S.value_measurable n)
      (by intro h hh r; simp only [carriedValue, if_pos hh.1, if_pos hh.2])]
    rw [Set.inter_comm (S.halt n)]

/-- Exact equality between execution that makes calls only while alive and the
fixed-T policy which remembers the first output and ignores subsequent replies. -/
theorem outputLaw_eq_padded (S : StoppingRule Seed Reply Output)
    (A : Policy Seed Query Reply Output T) (μ : Measure Seed) [IsProbabilityMeasure μ]
    (K : Kernel Query Reply) [IsMarkovKernel K] :
    S.outputLaw A μ K = (S.paddedPolicy A).outputLaw μ K := by
  unfold outputLaw Policy.outputLaw
  rw [paddedPolicy_historyLaw, exitedLaw_eq_restrict, liveLaw_eq_restrict]
  have hv : ((A.historyLaw μ K T).restrict (S.survival T)).map (S.value T) =
      ((A.historyLaw μ K T).restrict (S.survival T)).map (S.carriedValue T) := by
    apply Measure.map_congr
    filter_upwards [ae_restrict_mem (S.survival_measurable T)] with h hh
    exact (S.carriedValue_of_survival T h hh).symm
  rw [hv, ← Measure.map_add _ _ (S.carriedValue_measurable T),
    Measure.restrict_compl_add_restrict (S.survival_measurable T)]
  rfl

instance outputLaw_probability (S : StoppingRule Seed Reply Output)
    (A : Policy Seed Query Reply Output T) (μ : Measure Seed) [IsProbabilityMeasure μ]
    (K : Kernel Query Reply) [IsMarkovKernel K] : IsProbabilityMeasure (S.outputLaw A μ K) := by
  rw [S.outputLaw_eq_padded A μ K]
  infer_instance

/-- Fixed-horizon policies are included among bounded stopping policies. -/
def neverHalt (A : Policy Seed Query Reply Output T) (fallback : Output) :
    StoppingRule Seed Reply Output where
  halt _ := ∅
  halt_measurable _ := MeasurableSet.empty
  value n h := if hn : n = T then A.output (cast (congrArg (History Seed Reply) hn) h)
    else fallback
  value_measurable n := by
    by_cases hn : n = T
    · subst n
      simpa only [dif_pos rfl, cast_eq] using A.output_measurable
    · simpa only [dif_neg hn] using (measurable_const : Measurable (fun _ : History Seed Reply n => fallback))

theorem neverHalt_survival (A : Policy Seed Query Reply Output T) (fallback : Output) (n : ℕ) :
    (neverHalt A fallback).survival n = Set.univ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [survival, ih]
    simp only [neverHalt, compl_empty, inter_self, preimage_univ]

theorem neverHalt_outputLaw (A : Policy Seed Query Reply Output T) (fallback : Output)
    (μ : Measure Seed) [IsProbabilityMeasure μ] (K : Kernel Query Reply) [IsMarkovKernel K] :
    (neverHalt A fallback).outputLaw A μ K = A.outputLaw μ K := by
  rw [outputLaw_eq_padded]
  unfold Policy.outputLaw
  rw [paddedPolicy_historyLaw]
  congr 1
  funext h
  change (neverHalt A fallback).carriedValue T h = A.output h
  rw [carriedValue_of_survival _ T h (by rw [neverHalt_survival]; exact Set.mem_univ _)]
  simp [neverHalt]

/-- Output law for the uncapped stopping procedure, as the countable disjoint
sum of its first-exit laws. Paths that never halt contribute no output mass. -/
def eventualOutputLaw (S : StoppingRule Seed Reply Output)
    (A : Policy Seed Query Reply Output T) (μ : Measure Seed) (K : Kernel Query Reply) :
    Measure Output :=
  Measure.sum fun n => ((S.liveLaw A μ K n).restrict (S.halt n)).map (S.value n)

theorem exitedLaw_eq_sum_range (S : StoppingRule Seed Reply Output)
    (A : Policy Seed Query Reply Output T) (μ : Measure Seed) (K : Kernel Query Reply) (n : ℕ) :
    S.exitedLaw A μ K n = ∑ i ∈ Finset.range n,
      ((S.liveLaw A μ K i).restrict (S.halt i)).map (S.value i) := by
  induction n with
  | zero => simp only [exitedLaw, Finset.range_zero, Finset.sum_empty]
  | succ n ih => simp only [exitedLaw, ih, Finset.sum_range_succ]

/-- An almost-sure bound on raw calls is expressed before sampling: the
survivor measure which would request call T+1 is zero. Under this bound the
uncapped exit law agrees exactly with the capped stopped execution. -/
theorem eventualOutputLaw_eq_capped (S : StoppingRule Seed Reply Output)
    (A : Policy Seed Query Reply Output T) (μ : Measure Seed) [IsProbabilityMeasure μ]
    (K : Kernel Query Reply) [IsMarkovKernel K]
    (hbudget : (S.liveLaw A μ K T).restrict (S.halt T)ᶜ = 0) :
    S.eventualOutputLaw A μ K = S.outputLaw A μ K := by
  have hbase : S.liveLaw A μ K (T + 1) = 0 := by
    rw [liveLaw, hbudget, Measure.compProd_zero_left]
  have hzero (n : ℕ) (hn : T + 1 ≤ n) : S.liveLaw A μ K n = 0 := by
    induction n, hn using Nat.le_induction with
    | base => exact hbase
    | succ n hn ih => simp only [liveLaw, ih, Measure.restrict_zero, Measure.compProd_zero_left]
  have hsum : S.eventualOutputLaw A μ K = S.exitedLaw A μ K (T + 1) := by
    ext C hC
    rw [eventualOutputLaw, Measure.sum_apply _ hC, exitedLaw_eq_sum_range,
      Measure.finset_sum_apply]
    apply tsum_eq_sum
    intro n hn
    have hle : T + 1 ≤ n := Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hn)
    simp only [hzero n hle, Measure.restrict_zero, Measure.map_zero, Measure.coe_zero, Pi.zero_apply]
  rw [hsum, exitedLaw]
  have hrestrict : (S.liveLaw A μ K T).restrict (S.halt T) = S.liveLaw A μ K T := by
    have hh := Measure.restrict_add_restrict_compl (μ := S.liveLaw A μ K T) (S.halt_measurable T)
    simpa only [hbudget, add_zero] using hh
  rw [hrestrict]
  rfl

theorem eventualOutputLaw_eq_padded (S : StoppingRule Seed Reply Output)
    (A : Policy Seed Query Reply Output T) (μ : Measure Seed) [IsProbabilityMeasure μ]
    (K : Kernel Query Reply) [IsMarkovKernel K]
    (hbudget : (S.liveLaw A μ K T).restrict (S.halt T)ᶜ = 0) :
    S.eventualOutputLaw A μ K = (S.paddedPolicy A).outputLaw μ K :=
  (S.eventualOutputLaw_eq_capped A μ K hbudget).trans (S.outputLaw_eq_padded A μ K)

/-- Execute exactly T calls, then halt. This embeds fixed-horizon algorithms in
the class of uncapped rules whose call count is almost surely at most T. -/
def terminalHalt (A : Policy Seed Query Reply Output T) (fallback : Output) :
    StoppingRule Seed Reply Output where
  halt n := if n < T then ∅ else Set.univ
  halt_measurable n := by split_ifs <;> measurability
  value := (neverHalt A fallback).value
  value_measurable := (neverHalt A fallback).value_measurable

theorem terminalHalt_survival (A : Policy Seed Query Reply Output T) (fallback : Output)
    (n : ℕ) (hn : n ≤ T) : (terminalHalt A fallback).survival n = Set.univ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hnT : n < T := by omega
    rw [survival, ih (by omega)]
    simp only [terminalHalt, if_pos hnT, compl_empty, inter_self, preimage_univ]

theorem terminalHalt_budget (A : Policy Seed Query Reply Output T) (fallback : Output)
    (μ : Measure Seed) (K : Kernel Query Reply) :
    ((terminalHalt A fallback).liveLaw A μ K T).restrict
      ((terminalHalt A fallback).halt T)ᶜ = 0 := by
  simp only [terminalHalt, lt_self_iff_false, if_false, compl_univ, Measure.restrict_empty]

theorem terminalHalt_eventualOutputLaw (A : Policy Seed Query Reply Output T) (fallback : Output)
    (μ : Measure Seed) [IsProbabilityMeasure μ] (K : Kernel Query Reply) [IsMarkovKernel K] :
    (terminalHalt A fallback).eventualOutputLaw A μ K = A.outputLaw μ K := by
  rw [eventualOutputLaw_eq_padded _ A μ K (terminalHalt_budget A fallback μ K)]
  unfold Policy.outputLaw
  rw [paddedPolicy_historyLaw]
  congr 1
  funext h
  change (terminalHalt A fallback).carriedValue T h = A.output h
  rw [carriedValue_of_survival _ T h (by
    rw [terminalHalt_survival A fallback T le_rfl]; exact Set.mem_univ _)]
  simp [terminalHalt, neverHalt]

end StoppingRule
end HeavyTail.AdaptiveKernel
