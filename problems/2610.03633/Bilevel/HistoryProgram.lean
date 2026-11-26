import Bilevel.BorelAdaptiveExecution
import Bilevel.HistoryOracle
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-! Execution kernels for every measurable adaptive program, with a general
history-dependent joint response law. Halting is absorbing. No oracle-code
syntax restriction, iid realization, or standard-Borel algorithm-state
assumption is imposed. This file is an execution foundation; it does not
assert an already completed history-dependent minimax comparison. -/
noncomputable section
open MeasureTheory ProbabilityTheory Preorder

namespace Bilevel.HistoryProgram

variable {S Q O Y H : Type*} [MeasurableSpace S] [MeasurableSpace Q]
  [MeasurableSpace O] [MeasurableSpace Y] [MeasurableSpace H]

/-- A shared conditional response law and the history update after that
same response. Moment hypotheses are supplied by the SFO interface. -/
structure Oracle (Q O H : Type*) [MeasurableSpace Q] [MeasurableSpace O]
    [MeasurableSpace H] where
  law : Kernel (Q × H) O
  markov : IsMarkovKernel law
  update : (Q × H) × O → H
  update_measurable : Measurable update

attribute [instance] Oracle.markov

variable (A : BorelAdaptive.Program S Q O Y) (R : Oracle Q O H)

def request (z : S × H) : Q × H := (A.query z.1,z.2)

theorem request_measurable : Measurable (request A (H := H)) :=
  (A.query_measurable.comp measurable_fst).prodMk measurable_snd

def advance (z : (S × H) × O) : S × H :=
  (A.update (z.1.1,z.2),R.update (request A z.1,z.2))

theorem advance_measurable : Measurable (advance A R) :=
  (A.update_measurable.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).prodMk
    (R.update_measurable.comp (((request_measurable A).comp measurable_fst).prodMk measurable_snd))

/-- One actual call while the program is live. The same full observation
updates both algorithm state and oracle history. -/
def liveStep : Kernel (S × H) (S × H) :=
  Stateful.KernelMap.dependent (R.law.comap (request A) (request_measurable A)) (advance A R)

instance liveStep_markov : IsMarkovKernel (liveStep A R) :=
  Stateful.KernelMap.dependent_markov _ _ (advance_measurable A R)

theorem liveStep_apply (z : S × H) :
    liveStep A R z = (R.law (request A z)).map (fun o => advance A R (z,o)) :=
  Stateful.KernelMap.dependent_apply _ _ (advance_measurable A R) z

abbrev halted : Set (S × H) := {z | A.halt z.1 = true}

theorem halted_measurable : MeasurableSet (halted A (H := H)) :=
  (A.halt_measurable.comp measurable_fst) (measurableSet_singleton true)

/-- Halted configurations make no further call and retain their history. -/
def step : Kernel (S × H) (S × H) :=
  Kernel.piecewise (halted_measurable A) Kernel.id (liveStep A R)

instance step_markov : IsMarkovKernel (step A R) := by
  unfold step
  infer_instance

theorem step_halted (z : S × H) (hz : A.halt z.1 = true) :
    step A R z = Measure.dirac z := by
  simp [step,Kernel.piecewise_apply,halted,hz,Kernel.id_apply]

theorem step_live (z : S × H) (hz : A.halt z.1 = false) :
    step A R z = (R.law (request A z)).map (fun o => advance A R (z,o)) := by
  simp [step,Kernel.piecewise_apply,halted,hz,liveStep_apply]

/-- Distribution after `n` transitions, including absorbing halted states. -/
def run : ℕ → Kernel (S × H) (S × H)
  | 0 => Kernel.id
  | n+1 => step A R ∘ₖ run n

instance run_markov (n : ℕ) : IsMarkovKernel (run A R n) := by
  induction n with
  | zero => exact inferInstanceAs (IsMarkovKernel Kernel.id)
  | succ n ih =>
      change IsMarkovKernel (step A R ∘ₖ run A R n)
      infer_instance

@[simp] theorem run_zero : run A R 0 = Kernel.id := rfl

@[simp] theorem run_succ (n : ℕ) : run A R (n+1) = step A R ∘ₖ run A R n := rfl

theorem run_add (n m : ℕ) : run A R (n+m) = run A R m ∘ₖ run A R n := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.add_succ,run_succ,ih,run_succ,Kernel.comp_assoc]

theorem run_halted (z : S × H) (hz : A.halt z.1 = true) (n : ℕ) :
    run A R n z = Measure.dirac z := by
  induction n with
  | zero => exact Kernel.id_apply z
  | succ n ih =>
      rw [run_succ,Kernel.comp_apply,ih,Measure.dirac_bind (Kernel.measurable _)]
      exact step_halted A R z hz

/-- Arbitrary private randomness is integrated only through the measurable
initial algorithm state; the hidden oracle does not choose that state. -/
def runLaw {Private : Type*} [MeasurableSpace Private]
    (privateLaw : Measure Private) (start : Private → S)
    (h₀ : H) (n : ℕ) : Measure (S × H) :=
  run A R n ∘ₘ privateLaw.map (fun r => (start r,h₀))

instance runLaw_probability {Private : Type*} [MeasurableSpace Private]
    (privateLaw : Measure Private) [IsProbabilityMeasure privateLaw]
    (start : Private → S) (hs : Measurable start) (h₀ : H) (n : ℕ) :
    IsProbabilityMeasure (runLaw A R privateLaw start h₀ n) := by
  have : IsProbabilityMeasure (privateLaw.map (fun r => (start r,h₀))) :=
    isProbabilityMeasure_map (hs.prodMk measurable_const).aemeasurable
  unfold runLaw
  infer_instance

/-- Prefix-dependent form of the transition kernel accepted directly by
Mathlib's Ionescu-Tulcea construction. -/
def last (n : ℕ) (z : Π _ : Finset.Iic n, S × H) : S × H :=
  z ⟨n,Finset.mem_Iic.mpr le_rfl⟩

theorem last_measurable (n : ℕ) : Measurable (last (S := S) (H := H) n) :=
  measurable_pi_apply _

def nextKernel (n : ℕ) : Kernel (Π _ : Finset.Iic n, S × H) (S × H) :=
  (step A R).comap (last n) (last_measurable n)

instance nextKernel_markov (n : ℕ) : IsMarkovKernel (nextKernel A R n) := by
  unfold nextKernel
  infer_instance

/-- The full infinite execution law exists even for arbitrary measurable
algorithm states. Exact stopping/output bridges can be built on this law. -/
def trajectory : Kernel (Π _ : Finset.Iic 0, S × H) (ℕ → S × H) :=
  Kernel.traj (X := fun _ => S × H) (nextKernel A R) 0

instance trajectory_markov : IsMarkovKernel (trajectory A R) := by
  unfold trajectory
  infer_instance

theorem trajectory_finite_marginal (n : ℕ) :
    (trajectory A R).map (frestrictLe n) =
      Kernel.partialTraj (X := fun _ => S × H) (nextKernel A R) 0 n :=
  Kernel.traj_map_frestrictLe 0 n

theorem partial_one_step_endpoint (n : ℕ) :
    (Kernel.partialTraj (X := fun _ => S × H) (nextKernel A R) n (n+1)).map (last (n+1)) =
      nextKernel A R n := by
  let e := MeasurableEquiv.piSingleton (X := fun _ => S × H) n
  have hl : last (S := S) (H := H) (n+1) ∘ IicProdIoc (X := fun _ => S × H) n (n+1) =
      e.symm ∘ Prod.snd := by
    funext z
    simp [last,Function.comp_def,IicProdIoc,e,MeasurableEquiv.piSingleton]
  have hg : Measurable (IicProdIoc (X := fun _ => S × H) n (n+1)) :=
    measurable_IicProdIoc
  rw [Kernel.partialTraj_succ_self,
    ← Kernel.map_comp_right _ hg (last_measurable (S := S) (H := H) (n+1)),hl,
    Kernel.map_comp_right _ measurable_snd e.symm.measurable]
  rw [← Kernel.snd_eq,Kernel.snd_prod]
  change ((nextKernel A R n).map e).map e.symm = _
  rw [← Kernel.map_comp_right _ e.measurable e.symm.measurable]
  have he : e.symm ∘ e = id := by
    funext z
    exact e.symm_apply_apply z
  rw [he,Kernel.map_id]

/-- The endpoint of the Ionescu-Tulcea finite marginal is exactly the
iterated arbitrary-program transition kernel, not an abstract replacement. -/
theorem partial_endpoint (n : ℕ) :
    (Kernel.partialTraj (X := fun _ => S × H) (nextKernel A R) 0 n).map (last n) =
      (run A R n).comap (last 0) (last_measurable 0) := by
  induction n with
  | zero => simp [Kernel.partialTraj_self,Kernel.id_map (last_measurable 0),
      Kernel.id_comap (last_measurable 0)]
  | succ n ih =>
      rw [Kernel.partialTraj_succ_eq_comp (Nat.zero_le n),Kernel.map_comp,
        partial_one_step_endpoint]
      change (step A R).comap (last n) (last_measurable n) ∘ₖ _ = _
      rw [← Kernel.comp_map _ _ (last_measurable n),ih]
      rfl

theorem trajectory_endpoint (n : ℕ) :
    (trajectory A R).map (fun z => z n) =
      (run A R n).comap (last 0) (last_measurable 0) := by
  have he : (fun z : ℕ → S × H => z n) = last n ∘ frestrictLe n := rfl
  rw [he,Kernel.map_comp_right _ (measurable_frestrictLe n) (last_measurable n),
    trajectory_finite_marginal,partial_endpoint]

def initialPrefix (z : S × H) : Π _ : Finset.Iic 0, S × H := fun _ => z

theorem initialPrefix_measurable : Measurable (initialPrefix (S := S) (H := H)) := by
  unfold initialPrefix
  fun_prop

/-- Infinite execution measure including arbitrary private randomness. -/
def trajectoryLaw {Private : Type*} [MeasurableSpace Private]
    (privateLaw : Measure Private) (start : Private → S) (h₀ : H) : Measure (ℕ → S × H) :=
  trajectory A R ∘ₘ privateLaw.map (fun r => initialPrefix (start r,h₀))

instance trajectoryLaw_probability {Private : Type*} [MeasurableSpace Private]
    (privateLaw : Measure Private) [IsProbabilityMeasure privateLaw]
    (start : Private → S) (hs : Measurable start) (h₀ : H) :
    IsProbabilityMeasure (trajectoryLaw A R privateLaw start h₀) := by
  have : IsProbabilityMeasure (privateLaw.map (fun r => initialPrefix (start r,h₀))) :=
    isProbabilityMeasure_map (initialPrefix_measurable.comp (hs.prodMk measurable_const)).aemeasurable
  unfold trajectoryLaw
  infer_instance

theorem trajectoryLaw_endpoint {Private : Type*} [MeasurableSpace Private]
    (privateLaw : Measure Private) (start : Private → S) (hs : Measurable start)
    (h₀ : H) (n : ℕ) :
    (trajectoryLaw A R privateLaw start h₀).map (fun z => z n) =
      runLaw A R privateLaw start h₀ n := by
  rw [trajectoryLaw,Measure.map_comp _ _ (measurable_pi_apply n),trajectory_endpoint]
  have hm : Measurable (fun r => initialPrefix (start r,h₀)) :=
    initialPrefix_measurable.comp (hs.prodMk measurable_const)
  have hinit : (privateLaw.map (fun r => initialPrefix (start r,h₀))).map (last 0) =
      privateLaw.map (fun r => (start r,h₀)) := by
    rw [Measure.map_map (last_measurable 0) hm]
    rfl
  change ((run A R n).comap (last 0) (last_measurable 0)) ∘ₘ _ = _
  rw [← Kernel.comp_deterministic_eq_comap,← Measure.comp_assoc,
    Measure.deterministic_comp_eq_map,hinit]
  rfl

end Bilevel.HistoryProgram
