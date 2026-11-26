import Bilevel.BorelAdaptivePrior
import Bilevel.InfiniteBernoulli

/-! Adaptedness and fresh-coin independence for the actual halted execution.
The state after n steps is a measurable function of the private initial
state, the mean instance, and only the first n oracle draws. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Bilevel.BorelAdaptive

variable {S Q O Y I C Private : Type*} [MeasurableSpace S] [MeasurableSpace Q]
  [MeasurableSpace O] [MeasurableSpace Y] [MeasurableSpace I] [MeasurableSpace C]
  [MeasurableSpace Private]

omit [MeasurableSpace I] [MeasurableSpace C] in
theorem run_congr_draws (A : Program S Q O Y) (response : I → Q → C → O)
    (i : I) (x y : ℕ → C) (initial : S) (n : ℕ) (h : ∀ t < n, x t = y t) :
    run A response i x initial n = run A response i y initial n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [run,run,ih (fun t ht => h t (Nat.lt_succ_of_lt ht)),h n (Nat.lt_succ_self n)]

def finiteDraws [Inhabited C] (n : ℕ) (x : Fin n → C) (t : ℕ) : C :=
  if h : t < n then x ⟨t,h⟩ else default

theorem finiteDraws_measurable [Inhabited C] (n : ℕ) : Measurable (finiteDraws (C:=C) n) := by
  apply measurable_pi_lambda
  intro t
  unfold finiteDraws
  split_ifs with h
  · exact measurable_pi_apply (⟨t,h⟩ : Fin n)
  · exact measurable_const

def finiteRun [Inhabited C] (A : Program S Q O Y) (response : I → Q → C → O)
    (n : ℕ) (p : I × (S × (Fin n → C))) : S :=
  run A response p.1 (finiteDraws n p.2.2) p.2.1 n

theorem finiteRun_measurable [Inhabited C] (A : Program S Q O Y) (response : I → Q → C → O)
    (hr : Measurable (fun p : I × (Q × C) => response p.1 p.2.1 p.2.2)) (n : ℕ) :
    Measurable (finiteRun A response n) :=
  (run_measurable A response hr n).comp
    (measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
      ((finiteDraws_measurable n).comp (measurable_snd.comp measurable_snd))))

omit [MeasurableSpace I] [MeasurableSpace C] in
theorem run_eq_finiteRun [Inhabited C] (A : Program S Q O Y) (response : I → Q → C → O)
    (i : I) (x : ℕ → C) (initial : S) (n : ℕ) :
    run A response i x initial n = finiteRun A response n (i,(initial,fun t : Fin n => x t)) := by
  apply run_congr_draws
  intro t ht
  simp only [finiteDraws,dif_pos ht]

section Bernoulli
variable {I Private : Type} [MeasurableSpace I] [MeasurableSpace Private]

def bernoulliPastState (A : Program S Q O Y) (response : I → Q → Bool → O)
    (initial : Private → S) (n : ℕ) (p : (I × Private) × (Fin n → Bool)) : S :=
  finiteRun A response n (p.1.1,(initial p.1.2,p.2))

theorem bernoulliPastState_measurable (A : Program S Q O Y) (response : I → Q → Bool → O)
    (hr : Measurable (fun p : I × (Q × Bool) => response p.1 p.2.1 p.2.2))
    (initial : Private → S) (hi : Measurable initial) (n : ℕ) :
    Measurable (bernoulliPastState A response initial n) :=
  (finiteRun_measurable A response hr n).comp
    ((measurable_fst.comp measurable_fst).prodMk
      ((hi.comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd))

def bernoulliRun (A : Program S Q O Y) (response : I → Q → Bool → O)
    (initial : Private → S) (n : ℕ) (z : InfiniteBernoulli.Sample (I × Private)) : S :=
  run A response (z none).1 (fun t => z (some t)) (initial (z none).2) n

omit [MeasurableSpace I] [MeasurableSpace Private] in
theorem bernoulliRun_past (A : Program S Q O Y) (response : I → Q → Bool → O)
    (initial : Private → S) (n : ℕ) (z : InfiniteBernoulli.Sample (I × Private)) :
    bernoulliRun A response initial n z =
      bernoulliPastState A response initial n (InfiniteBernoulli.pastInput n z) :=
  run_eq_finiteRun A response _ _ _ n

theorem bernoulliRun_fresh_independent (A : Program S Q O Y) (response : I → Q → Bool → O)
    (hr : Measurable (fun p : I × (Q × Bool) => response p.1 p.2.1 p.2.2))
    (initial : Private → S) (hi : Measurable initial)
    (ν : Measure (I × Private)) [IsProbabilityMeasure ν] (p : ℝ) (hp : p ≤ 1) (n : ℕ) :
    IndepFun (bernoulliRun A response initial n)
      (fun z : InfiniteBernoulli.Sample (I × Private) => z (some n)) (InfiniteBernoulli.law ν p hp) := by
  have h := (InfiniteBernoulli.prefix_fresh_independent ν p hp n).comp
    (bernoulliPastState_measurable A response hr initial hi n) measurable_id
  simpa only [Function.comp_def,← bernoulliRun_past] using h

theorem bernoulliQuery_fresh_independent (A : Program S Q O Y) (response : I → Q → Bool → O)
    (hr : Measurable (fun p : I × (Q × Bool) => response p.1 p.2.1 p.2.2))
    (initial : Private → S) (hi : Measurable initial)
    (ν : Measure (I × Private)) [IsProbabilityMeasure ν] (p : ℝ) (hp : p ≤ 1) (n : ℕ) :
    IndepFun (fun z => A.query (bernoulliRun A response initial n z))
      (fun z : InfiniteBernoulli.Sample (I × Private) => z (some n)) (InfiniteBernoulli.law ν p hp) :=
  (bernoulliRun_fresh_independent A response hr initial hi ν p hp n).comp A.query_measurable measurable_id

end Bernoulli
end Bilevel.BorelAdaptive
