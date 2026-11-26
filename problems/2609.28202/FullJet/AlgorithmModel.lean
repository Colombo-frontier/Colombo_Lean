import FullJet.CapacityLowerBound

open MeasureTheory

namespace FullJet

/-- A full-jet algorithm has arbitrary internal state and arbitrary private
randomness. A fixed budget counts actual component-oracle replies. -/
structure JetAlgorithm (Ω E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (n p : ℕ) where
  State : Type
  query : Ω → State → Fin n × E
  update : Ω → State → JetPacket p E → State
  output : Ω → State → E
  initial : Ω → State

noncomputable def JetAlgorithm.result {Ω E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n p : ℕ} (A : JetAlgorithm Ω E n p) (N : ℕ) (f : Fin n → E → ℝ) (s : Ω) : E :=
  componentJetOutput (A.query s) (A.update s) (A.output s) (A.initial s) N f

def JetAlgorithm.measurableOn {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {n p : ℕ}
    (A : JetAlgorithm Ω E n p) (N : ℕ) (Δ L : ℝ) : Prop :=
  ∀ f, Admissible p n Δ L f → Measurable (fun s => ‖fderiv ℝ (average f) (A.result N f s)‖)

def JetAlgorithm.succeeds {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {n p : ℕ}
    (A : JetAlgorithm Ω E n p) (P : Measure Ω) (N : ℕ) (Δ L ε δ : ℝ) : Prop :=
  A.measurableOn N Δ L ∧ ∀ f, Admissible p n Δ L f →
    P.real {s | ε < ‖fderiv ℝ (average f) (A.result N f s)‖} ≤ δ

/-- An algorithm family covers every finite-dimensional real Euclidean
space, so the hard dimension may be chosen after fixing the query budget. -/
def UniformJetAlgorithm (Ω : Type*) (n p : ℕ) :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E],
    JetAlgorithm Ω E n p

def UniformJetAlgorithm.succeeds {Ω : Type*} [MeasurableSpace Ω] {n p : ℕ}
    (A : UniformJetAlgorithm Ω n p) (P : Measure Ω) (N : ℕ) (Δ L ε δ : ℝ) : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E],
    (A E).succeeds P N Δ L ε δ

theorem oracleRun_seed_state {Ω State Query Reply : Type*}
    (query : Ω → State → Query) (update : Ω → State → Reply → State)
    (initial : Ω → State) (oracle : Query → Reply) (s : Ω) (N : ℕ) :
    oracleRun (fun z : Ω × State => query z.1 z.2)
      (fun z r => (z.1, update z.1 z.2 r)) oracle (s, initial s) N =
      (s, oracleRun (query s) (update s) oracle (initial s) N) := by
  induction N with
  | zero => rfl
  | succ N ih => simp only [oracleRun, ih]

theorem scalar_seed_output {Ω State : Type*} {n p : ℕ}
    (query : Ω → State → Fin n × ℝ) (update : Ω → State → ScalarJet p → State)
    (output : Ω → State → ℝ) (initial : Ω → State) (N : ℕ) (f : Fin n → ℝ → ℝ) (s : Ω) :
    fullJetOutput (fun z : Ω × State => query z.1 z.2)
      (fun z r => (z.1, update z.1 z.2 r)) (fun z => output z.1 z.2) (s, initial s) N f =
      componentJetOutput (query s) (update s) (output s) (initial s) N f := by
  unfold fullJetOutput componentJetOutput
  rw [oracleRun_seed_state]
  rfl

theorem scalar_algorithm_budget_lower {Ω : Type*} [MeasurableSpace Ω] {n p N : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (A : JetAlgorithm Ω ℝ n p)
    (hn : 0 < n) (hp : 2 ≤ p) (Δ L ε δ : ℝ) (hΔ : 0 < Δ) (hL : 0 ≤ L) (hε : 0 < ε)
    (hδ : δ < 1 / 4) (hA : A.succeeds P N Δ L ε δ) : n < 2 * N := by
  by_contra h
  have hN : 2 * N ≤ n := by omega
  obtain ⟨f, hf, hh⟩ := rare_component_lower_bound hn hp P Δ ε L hΔ hε hL
    (fun z : Ω × A.State => A.query z.1 z.2)
    (fun z r => (z.1, A.update z.1 z.2 r))
    (fun z => A.output z.1 z.2) (fun s => (s, A.initial s)) N hN (fun f hf => by
      simp only [scalar_seed_output, norm_deriv_eq_norm_fderiv]
      exact measurableSet_lt measurable_const (hA.1 f hf))
  simp only [scalar_seed_output, norm_deriv_eq_norm_fderiv] at hh
  have hupper := hA.2 f hf
  exact (not_le_of_gt hδ) (hh.trans hupper)

end FullJet
