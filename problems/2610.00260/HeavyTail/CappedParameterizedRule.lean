import HeavyTail.CappedRawPolicy
import HeavyTail.AdaptiveKernelSeedMap

/-! Carry a public stage parameter unchanged in the actual raw-call state.
Joint measurability is explicit. Restriction to a fixed parameter is proved
pathwise against the original capped rule, including rejected observations. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace HeavyTail.CappedRaw
universe u v w
variable {C Reply : Type u} {State : Type v} {Query Output : Type w}
  [MeasurableSpace C] [MeasurableSpace Reply] [MeasurableSpace State]
  [MeasurableSpace Query] [MeasurableSpace Output]

def parameterizedRule (M : C → Rule State Query Reply Output)
    (hq : Measurable (fun s : C × State => (M s.1).query s.2))
    (ha : MeasurableSet {z : C × (State × Reply) | z.2 ∈ (M z.1).acceptance})
    (hu : Measurable (fun z : C × (State × Reply) => (M z.1).update z.2))
    (ho : Measurable (fun s : C × State => (M s.1).readout s.2)) :
    Rule (C × State) Query Reply Output where
  query s := (M s.1).query s.2
  query_measurable := hq
  acceptance := {z | (z.1.2, z.2) ∈ (M z.1.1).acceptance}
  acceptance_measurable := ha.preimage ((measurable_fst.comp measurable_fst).prodMk
    ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  update z := (z.1.1, (M z.1.1).update (z.1.2, z.2))
  update_measurable := (measurable_fst.comp measurable_fst).prodMk
    (hu.comp ((measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))
  readout s := (M s.1).readout s.2
  readout_measurable := ho

def fiberState (c : C) (s : ℕ × State) : ℕ × (C × State) := (s.1, (c, s.2))

theorem parameterizedRule_step (M : C → Rule State Query Reply Output)
    (hq : Measurable (fun s : C × State => (M s.1).query s.2))
    (ha : MeasurableSet {z : C × (State × Reply) | z.2 ∈ (M z.1).acceptance})
    (hu : Measurable (fun z : C × (State × Reply) => (M z.1).update z.2))
    (ho : Measurable (fun s : C × State => (M s.1).readout s.2))
    (c : C) (n : ℕ) (s : ℕ × State) (r : Reply) :
    (parameterizedRule M hq ha hu ho).step n (fiberState c s, r) =
      fiberState c ((M c).step n (s, r)) := by
  unfold Rule.step Rule.activeAcceptance parameterizedRule fiberState
  simp only [mem_setOf_eq]
  split_ifs <;> rfl

theorem parameterizedRule_state (M : C → Rule State Query Reply Output)
    (hq : Measurable (fun s : C × State => (M s.1).query s.2))
    (ha : MeasurableSet {z : C × (State × Reply) | z.2 ∈ (M z.1).acceptance})
    (hu : Measurable (fun z : C × (State × Reply) => (M z.1).update z.2))
    (ho : Measurable (fun s : C × State => (M s.1).readout s.2))
    (initial : C → State) (c : C) (n t : ℕ)
    (h : AdaptiveKernel.History PUnit Reply t) :
    (parameterizedRule M hq ha hu ho).state (fun c => (c, initial c)) n t
        (AdaptiveKernel.History.mapSeed (fun _ : PUnit => c) t h) =
      fiberState c ((M c).state (fun _ : PUnit => initial c) n t h) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change (parameterizedRule M hq ha hu ho).step n
      ((parameterizedRule M hq ha hu ho).state (fun c => (c, initial c)) n t
        (AdaptiveKernel.History.mapSeed (fun _ : PUnit => c) t h.1), h.2) = _
    rw [ih h.1, parameterizedRule_step]
    rfl

theorem parameterizedRule_policy_on_fiber (M : C → Rule State Query Reply Output)
    (hq : Measurable (fun s : C × State => (M s.1).query s.2))
    (ha : MeasurableSet {z : C × (State × Reply) | z.2 ∈ (M z.1).acceptance})
    (hu : Measurable (fun z : C × (State × Reply) => (M z.1).update z.2))
    (ho : Measurable (fun s : C × State => (M s.1).readout s.2))
    (initial : C → State) (hi : Measurable initial) (c : C) (n T : ℕ) :
    ((parameterizedRule M hq ha hu ho).policy (fun c => (c, initial c))
      (measurable_id.prodMk hi) n T).precomposeSeed (fun _ : PUnit => c) measurable_const =
      (M c).policy (fun _ : PUnit => initial c) measurable_const n T := by
  apply AdaptiveKernel.Policy.extensionality
  · intro t
    funext h
    change (parameterizedRule M hq ha hu ho).query
      ((parameterizedRule M hq ha hu ho).state (fun c => (c, initial c)) n t
        (AdaptiveKernel.History.mapSeed (fun _ : PUnit => c) t h)).2 = _
    rw [parameterizedRule_state]
    rfl
  · funext h
    change (parameterizedRule M hq ha hu ho).readout
      ((parameterizedRule M hq ha hu ho).state (fun c => (c, initial c)) n T
        (AdaptiveKernel.History.mapSeed (fun _ : PUnit => c) T h)).2 = _
    rw [parameterizedRule_state]
    rfl

theorem parameterizedRule_outputLaw_dirac (M : C → Rule State Query Reply Output)
    (hq : Measurable (fun s : C × State => (M s.1).query s.2))
    (ha : MeasurableSet {z : C × (State × Reply) | z.2 ∈ (M z.1).acceptance})
    (hu : Measurable (fun z : C × (State × Reply) => (M z.1).update z.2))
    (ho : Measurable (fun s : C × State => (M s.1).readout s.2))
    (initial : C → State) (hi : Measurable initial) (c : C) (n T : ℕ)
    (K : Kernel Query Reply) [IsMarkovKernel K] :
    ((parameterizedRule M hq ha hu ho).policy (fun c => (c, initial c))
      (measurable_id.prodMk hi) n T).outputLaw (Measure.dirac c) K =
      ((M c).policy (fun _ : PUnit => initial c) measurable_const n T).outputLaw
        (Measure.dirac PUnit.unit) K := by
  have h := AdaptiveKernel.Policy.precomposeSeed_dirac_outputLaw
    ((parameterizedRule M hq ha hu ho).policy (fun c => (c, initial c))
      (measurable_id.prodMk hi) n T) (fun _ : PUnit => c) measurable_const PUnit.unit K
  rw [parameterizedRule_policy_on_fiber M hq ha hu ho initial hi c n T] at h
  exact h.symm

end HeavyTail.CappedRaw
