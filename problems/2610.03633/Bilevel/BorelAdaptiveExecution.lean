import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Tactic

/-! Actual Borel adaptive execution with absorbing halting, independent of
the geometry of any hard instance. A state may contain the whole transcript
and private random seed. Every live step makes one original oracle call.
The finite cap returns the actual state reached after that many steps. -/
noncomputable section
open MeasureTheory
namespace Bilevel.BorelAdaptive

variable (S Q O Y : Type*) [MeasurableSpace S] [MeasurableSpace Q] [MeasurableSpace O] [MeasurableSpace Y]

structure Program where
  query : S → Q
  query_measurable : Measurable query
  update : S × O → S
  update_measurable : Measurable update
  halt : S → Bool
  halt_measurable : Measurable halt
  output : S → Y
  output_measurable : Measurable output

variable {S Q O Y} {I C : Type*} [MeasurableSpace I] [MeasurableSpace C]

def step (A : Program S Q O Y) (response : I → Q → C → O) (i : I) (c : C) (s : S) : S :=
  if A.halt s then s else A.update (s,response i (A.query s) c)

def run (A : Program S Q O Y) (response : I → Q → C → O) (i : I) (draws : ℕ → C) (initial : S) : ℕ → S
  | 0 => initial
  | t+1 => step A response i (draws t) (run A response i draws initial t)

abbrev Sample (I S C : Type*) := I × (S × (ℕ → C))

theorem step_measurable (A : Program S Q O Y) (response : I → Q → C → O)
    (hr : Measurable (fun p : I × (Q × C) => response p.1 p.2.1 p.2.2)) :
    Measurable (fun p : (I × C) × S => step A response p.1.1 p.1.2 p.2) := by
  have hh : MeasurableSet {p : (I × C) × S | A.halt p.2=true} :=
    (A.halt_measurable.comp measurable_snd) (measurableSet_singleton true)
  have ho := hr.comp ((measurable_fst.comp measurable_fst).prodMk
    ((A.query_measurable.comp measurable_snd).prodMk (measurable_snd.comp measurable_fst)))
  exact measurable_snd.ite hh (A.update_measurable.comp (measurable_snd.prodMk ho))

theorem run_measurable (A : Program S Q O Y) (response : I → Q → C → O)
    (hr : Measurable (fun p : I × (Q × C) => response p.1 p.2.1 p.2.2)) (n : ℕ) :
    Measurable (fun p : Sample I S C => run A response p.1 p.2.2 p.2.1 n) := by
  induction n with
  | zero => exact measurable_fst.comp measurable_snd
  | succ n ih =>
    exact (step_measurable A response hr).comp
      ((measurable_fst.prodMk ((measurable_pi_apply n).comp (measurable_snd.comp measurable_snd))).prodMk ih)

omit [MeasurableSpace I] [MeasurableSpace C] in
theorem step_halted (A : Program S Q O Y) (response : I → Q → C → O)
    (i : I) (c : C) (s : S) (hs : A.halt s=true) : step A response i c s=s := by
  simp [step,hs]

omit [MeasurableSpace I] [MeasurableSpace C] in
theorem run_halted_add (A : Program S Q O Y) (response : I → Q → C → O)
    (i : I) (draws : ℕ → C) (initial : S) (n : ℕ)
    (hn : A.halt (run A response i draws initial n)=true) (k : ℕ) :
    run A response i draws initial (n+k)=run A response i draws initial n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.add_succ,run,ih]
    exact step_halted A response i _ _ hn

def Terminated (A : Program S Q O Y) (response : I → Q → C → O) (p : Sample I S C) : Prop :=
  ∃ n,A.halt (run A response p.1 p.2.2 p.2.1 n)=true

theorem terminated_measurable (A : Program S Q O Y) (response : I → Q → C → O)
    (hr : Measurable (fun p : I × (Q × C) => response p.1 p.2.1 p.2.2)) :
    MeasurableSet {p | Terminated A response p} := by
  have hn (n : ℕ) : MeasurableSet {p : Sample I S C | A.halt (run A response p.1 p.2.2 p.2.1 n)=true} :=
    (A.halt_measurable.comp (run_measurable A response hr n)) (measurableSet_singleton true)
  simpa only [Terminated,Set.iUnion_setOf] using MeasurableSet.iUnion hn

open Classical in
def stopTime (A : Program S Q O Y) (response : I → Q → C → O) (p : Sample I S C) : ℕ :=
  if hp : Terminated A response p then Nat.find hp else 0

theorem stopTime_measurable (A : Program S Q O Y) (response : I → Q → C → O)
    (hr : Measurable (fun p : I × (Q × C) => response p.1 p.2.1 p.2.2)) :
    Measurable (stopTime A response) := by
  classical
  let T : Set (Sample I S C) := {p | Terminated A response p}
  have hm : Measurable (fun p : T => Nat.find p.property) := by
    apply measurable_find (fun p : T => p.property)
    intro n
    exact ((A.halt_measurable.comp (run_measurable A response hr n)).comp measurable_subtype_coe)
      (measurableSet_singleton true)
  exact hm.dite measurable_const (terminated_measurable A response hr)

omit [MeasurableSpace I] [MeasurableSpace C] in
theorem stopTime_halted (A : Program S Q O Y) (response : I → Q → C → O)
    (p : Sample I S C) (hp : Terminated A response p) :
    A.halt (run A response p.1 p.2.2 p.2.1 (stopTime A response p))=true := by
  simp only [stopTime,dif_pos hp]
  exact Nat.find_spec hp

omit [MeasurableSpace I] [MeasurableSpace C] in
theorem stopTime_first (A : Program S Q O Y) (response : I → Q → C → O)
    (p : Sample I S C) (hp : Terminated A response p) (t : ℕ) (ht : t<stopTime A response p) :
    A.halt (run A response p.1 p.2.2 p.2.1 t)=false := by
  rw [stopTime,dif_pos hp] at ht
  have hn := Nat.find_min hp ht
  exact Bool.eq_false_of_not_eq_true hn

def cappedOutput (A : Program S Q O Y) (response : I → Q → C → O) (n : ℕ) (p : Sample I S C) : Y :=
  A.output (run A response p.1 p.2.2 p.2.1 n)

def stoppedOutput (A : Program S Q O Y) (response : I → Q → C → O) (p : Sample I S C) : Y :=
  cappedOutput A response (stopTime A response p) p

theorem cappedOutput_measurable (A : Program S Q O Y) (response : I → Q → C → O)
    (hr : Measurable (fun p : I × (Q × C) => response p.1 p.2.1 p.2.2)) (n : ℕ) :
    Measurable (cappedOutput A response n) :=
  A.output_measurable.comp (run_measurable A response hr n)

theorem stoppedOutput_measurable (A : Program S Q O Y) (response : I → Q → C → O)
    (hr : Measurable (fun p : I × (Q × C) => response p.1 p.2.1 p.2.2)) :
    Measurable (stoppedOutput A response) := by
  have hm : Measurable (fun p : Sample I S C × ℕ => cappedOutput A response p.2 p.1) :=
    measurable_from_prod_countable (cappedOutput_measurable A response hr)
  exact hm.comp (measurable_id.prodMk (stopTime_measurable A response hr))

omit [MeasurableSpace I] [MeasurableSpace C] in
theorem cappedOutput_agrees (A : Program S Q O Y) (response : I → Q → C → O)
    (p : Sample I S C) (hp : Terminated A response p) (n : ℕ) (hn : stopTime A response p≤n) :
    cappedOutput A response n p=stoppedOutput A response p := by
  have hh := run_halted_add A response p.1 p.2.2 p.2.1 (stopTime A response p)
    (stopTime_halted A response p hp) (n-stopTime A response p)
  rw [Nat.add_sub_of_le hn] at hh
  exact congrArg A.output hh

end Bilevel.BorelAdaptive

