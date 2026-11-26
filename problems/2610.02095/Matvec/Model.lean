import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
Concrete fixed-horizon randomized two-sided oracle model for `matvec.tex`.
Queries are unrestricted real vectors. An algorithm's seed is sampled from
one probability measure independent of the input matrix. Early termination
can be represented by zero-query padding. `MainSequenceLowerBounds` is the
unproved target proposition, not an axiom or a theorem.
-/
namespace Matvec
open Matrix MeasureTheory
open scoped Matrix

abbrev Vec (n : ℕ) := Fin n → ℝ
abbrev Payoff (m n : ℕ) := Matrix (Fin m) (Fin n) ℝ
abbrev Query (m n : ℕ) := Vec n × Vec m
abbrev Reply (m n : ℕ) := Vec m × Vec n

instance payoffMeasurableSpace (m n : ℕ) : MeasurableSpace (Payoff m n) :=
  inferInstanceAs (MeasurableSpace (Fin m → Fin n → ℝ))

instance payoffBorelSpace (m n : ℕ) : BorelSpace (Payoff m n) :=
  inferInstanceAs (BorelSpace (Fin m → Fin n → ℝ))

def oracle {m n : ℕ} (A : Payoff m n) (q : Query m n) : Reply m n :=
  (A *ᵥ q.1, A.transpose *ᵥ q.2)

def SimplexFeasible {n : ℕ} (x : Vec n) : Prop :=
  (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1

def InBall {n : ℕ} (x : Vec n) : Prop := ∑ i, (x i) ^ 2 ≤ 1

inductive Geometry where
  | ballSimplex
  | simplexSimplex

def PrimalFeasible (g : Geometry) {n : ℕ} (x : Vec n) : Prop :=
  match g with
  | .ballSimplex => InBall x
  | .simplexSimplex => SimplexFeasible x

def Admissible (g : Geometry) {m n : ℕ} (A : Payoff m n) : Prop :=
  match g with
  | .ballSimplex => ∀ i, ∑ j, (A i j) ^ 2 ≤ 1
  | .simplexSimplex => ∀ i j, |A i j| ≤ 1

def payoff {m n : ℕ} (A : Payoff m n) (x : Vec n) (y : Vec m) : ℝ :=
  y ⬝ᵥ (A *ᵥ x)

/-- Universal comparison formulation of full saddle-point gap ≤ ε.
For the compact strategy domains this is exactly the max-minus-min condition.
It also records feasibility of the returned strategies. -/
def GameSuccess (g : Geometry) {m n : ℕ} (A : Payoff m n) (ε : ℝ)
    (out : Query m n) : Prop :=
  PrimalFeasible g out.1 ∧ SimplexFeasible out.2 ∧
  ∀ x y, PrimalFeasible g x → SimplexFeasible y →
    payoff A out.1 y - payoff A x out.2 ≤ ε

structure Algorithm (m n T : ℕ) (Seed : Type*) [MeasurableSpace Seed] where
  query : (j : ℕ) → Seed → (Fin j → Reply m n) → Query m n
  query_measurable : ∀ j, Measurable (fun p : Seed × (Fin j → Reply m n) => query j p.1 p.2)
  output : Seed → (Fin T → Reply m n) → Query m n
  output_measurable : Measurable (fun p : Seed × (Fin T → Reply m n) => output p.1 p.2)

def Algorithm.transcript {m n T : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (alg : Algorithm m n T Seed) (A : Payoff m n) (seed : Seed) :
    (j : ℕ) → (Fin j → Reply m n)
  | 0 => Fin.elim0
  | j + 1 => Fin.snoc (alg.transcript A seed j)
      (oracle A (alg.query j seed (alg.transcript A seed j)))

def Algorithm.run {m n T : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (alg : Algorithm m n T Seed) (A : Payoff m n) (seed : Seed) : Query m n :=
  alg.output seed (alg.transcript A seed T)

theorem measurable_oracle {m n : ℕ} (A : Payoff m n) : Measurable (oracle A) := by
  unfold oracle
  apply Measurable.prodMk
  all_goals
    apply measurable_pi_lambda
    intro i
    simp only [Matrix.mulVec, dotProduct]
    fun_prop

theorem Algorithm.measurable_transcript {m n T : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (alg : Algorithm m n T Seed) (A : Payoff m n) (j : ℕ) :
    Measurable (fun seed => alg.transcript A seed j) := by
  induction j with
  | zero => exact measurable_const
  | succ j ih =>
    apply measurable_pi_lambda
    intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp only [Algorithm.transcript, Fin.snoc_last]
      exact (measurable_oracle A).comp ((alg.query_measurable j).comp
        (measurable_id.prodMk ih))
    · simpa only [Algorithm.transcript, Fin.snoc_castSucc] using
        (measurable_pi_apply i).comp ih

theorem Algorithm.measurable_run {m n T : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (alg : Algorithm m n T Seed) (A : Payoff m n) : Measurable (alg.run A) :=
  alg.output_measurable.comp (measurable_id.prodMk (alg.measurable_transcript A T))

def Solves {m n T : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (alg : Algorithm m n T Seed) (μ : Measure Seed) (g : Geometry) (ε : ℝ) : Prop :=
  ∀ A : Payoff m n, Admissible g A →
    (2 / 3 : ℝ) ≤ μ.real {seed | GameSuccess g A ε (alg.run A seed)}

theorem GameSuccess.mono {m n : ℕ} {g : Geometry} {A : Payoff m n}
    {ε δ : ℝ} {out : Query m n} (h : GameSuccess g A ε out) (hεδ : ε ≤ δ) :
    GameSuccess g A δ out := by
  exact ⟨h.1, h.2.1, fun x y hx hy => (h.2.2 x y hx hy).trans hεδ⟩

theorem Solves.mono {m n T : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {alg : Algorithm m n T Seed} {μ : Measure Seed} [IsProbabilityMeasure μ]
    {g : Geometry} {ε δ : ℝ} (h : Solves alg μ g ε) (hεδ : ε ≤ δ) :
    Solves alg μ g δ := by
  intro A hA
  exact (h A hA).trans (measureReal_mono (fun _ hs => hs.mono hεδ))

noncomputable def sourceRate (N : ℕ) : ℝ :=
  N / ((Real.log (N + 2)) ^ 2 * Real.log (Real.log (N + Real.exp (Real.exp 1))))

/-- The main theorem target, with actual randomized algorithms and actual
matrix games. No proof of this proposition is asserted by this file. -/
def MainSequenceLowerBounds : Prop :=
  ∃ c₀ c₁ c₂ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧ 0 < c₂ ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    (∀ (T : ℕ) (Seed : Type) [MeasurableSpace Seed]
      (alg : Algorithm (4 * N) (2 * N + 1) T Seed)
      (μ : Measure Seed), IsProbabilityMeasure μ →
      Solves alg μ .ballSimplex (c₀ / (N : ℝ) ^ (3 / 2 : ℝ)) →
      c₂ * sourceRate N ≤ T) ∧
    (∀ (T : ℕ) (Seed : Type) [MeasurableSpace Seed]
      (alg : Algorithm (4 * N) (4 * N) T Seed)
      (μ : Measure Seed), IsProbabilityMeasure μ →
      Solves alg μ .simplexSimplex
        (c₁ / ((N : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (Real.log (N + 2)))) →
      c₂ * sourceRate N ≤ T)

end Matvec

