import Matvec.DimensionExtension
import Matvec.ModelGapBridge
import Matvec.PolicyOracleMap

/-! Actual same-horizon randomized algorithm transfer from larger dimensions
to a smaller simplex hard core. All maps are Borel and the seed law is unchanged. -/
namespace Matvec
open MeasureTheory Matrix MeasurableSimulation
open scoped Matrix
noncomputable section
universe u

def algorithmOfPolicy {m n T : ℕ} {Seed : Type u} [MeasurableSpace Seed]
    (alg : Policy (Query m n) (Reply m n) (Query m n) T Seed) : Algorithm m n T Seed where
  query := alg.query
  query_measurable := alg.query_measurable
  output := alg.output
  output_measurable := alg.output_measurable

theorem algorithmOfPolicy_transcript {m n T : ℕ} {Seed : Type u} [MeasurableSpace Seed]
    (alg : Policy (Query m n) (Reply m n) (Query m n) T Seed)
    (A : Payoff m n) (seed : Seed) (j : ℕ) :
    (algorithmOfPolicy alg).transcript A seed j = alg.transcript (oracle A) seed j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Algorithm.transcript, Policy.transcript, ih]; rfl

theorem algorithmOfPolicy_run {m n T : ℕ} {Seed : Type u} [MeasurableSpace Seed]
    (alg : Policy (Query m n) (Reply m n) (Query m n) T Seed)
    (A : Payoff m n) (seed : Seed) :
    (algorithmOfPolicy alg).run A seed = alg.run (oracle A) seed := by
  change alg.output seed _ = alg.output seed _
  rw [algorithmOfPolicy_transcript]

namespace DimensionExtension

def aggregateQuery {m n M N : ℕ} (ρ : Fin M → Fin m) (χ : Fin N → Fin n)
    (q : Query M N) : Query m n := (aggregate χ q.1, aggregate ρ q.2)

theorem measurable_aggregateQuery {m n M N : ℕ} (ρ : Fin M → Fin m) (χ : Fin N → Fin n) :
    Measurable (aggregateQuery ρ χ) :=
  ((measurable_aggregate χ).comp measurable_fst).prodMk
    ((measurable_aggregate ρ).comp measurable_snd)

def duplicateReply {m n M N : ℕ} (ρ : Fin M → Fin m) (χ : Fin N → Fin n)
    (r : Reply m n) : Reply M N := (fun i => r.1 (ρ i), fun j => r.2 (χ j))

theorem measurable_duplicateReply {m n M N : ℕ} (ρ : Fin M → Fin m) (χ : Fin N → Fin n) :
    Measurable (duplicateReply ρ χ) :=
  ((continuous_duplicate_vector ρ).measurable.comp measurable_fst).prodMk
    ((continuous_duplicate_vector χ).measurable.comp measurable_snd)

theorem duplicate_oracle {m n M N : ℕ} (A : Payoff m n)
    (ρ : Fin M → Fin m) (χ : Fin N → Fin n) :
    duplicateReply ρ χ ∘ oracle A ∘ aggregateQuery ρ χ = oracle (duplicateMatrix A ρ χ) := by
  funext q
  apply Prod.ext
  · exact (duplicate_mulVec A ρ χ q.1).symm
  · exact (duplicate_transpose_mulVec A ρ χ q.2).symm

def duplicateAlgorithm {m n M N T : ℕ} {Seed : Type u} [MeasurableSpace Seed]
    (alg : Algorithm M N T Seed) (ρ : Fin M → Fin m) (χ : Fin N → Fin n) :
    Algorithm m n T Seed :=
  algorithmOfPolicy (((ofAlgorithm alg).mapOracle (aggregateQuery ρ χ) (duplicateReply ρ χ)
    (measurable_aggregateQuery ρ χ) (measurable_duplicateReply ρ χ)).mapOutput
    (fun _ q => aggregateQuery ρ χ q) ((measurable_aggregateQuery ρ χ).comp measurable_snd))

theorem duplicateAlgorithm_run {m n M N T : ℕ} {Seed : Type u} [MeasurableSpace Seed]
    (alg : Algorithm M N T Seed) (ρ : Fin M → Fin m) (χ : Fin N → Fin n)
    (A : Payoff m n) (seed : Seed) :
    (duplicateAlgorithm alg ρ χ).run A seed =
      aggregateQuery ρ χ (alg.run (duplicateMatrix A ρ χ) seed) := by
  rw [duplicateAlgorithm, algorithmOfPolicy_run, Policy.mapOutput_run, Policy.mapOracle_run,
    duplicate_oracle, ofAlgorithm_run]

theorem duplicateAlgorithm_solves {m n M N T : ℕ} {Seed : Type u} [MeasurableSpace Seed]
    (alg : Algorithm M N T Seed) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (ρ : Fin M → Fin m) (χ : Fin N → Fin n) (hρ : Function.Surjective ρ)
    (hχ : Function.Surjective χ) (ε : ℝ) (hsolve : Solves alg ν .simplexSimplex ε) :
    Solves (duplicateAlgorithm alg ρ χ) ν .simplexSimplex ε := by
  intro A hA
  have hlarge := hsolve (duplicateMatrix A ρ χ) (duplicate_entries_bounded A ρ χ hA)
  apply hlarge.trans
  apply measureReal_mono ?_ (measure_ne_top _ _)
  intro seed hs
  change GameSuccess .simplexSimplex A ε ((duplicateAlgorithm alg ρ χ).run A seed)
  rw [duplicateAlgorithm_run]
  obtain ⟨hx, hy, hgap⟩ := gameSuccess_simplex_fullGap _ ε _ hs
  exact fullGapAtMost_gameSuccess A _ _ ε (aggregate_simplex χ _ hx) (aggregate_simplex ρ _ hy)
    ((duplicate_fullGap_iff A ρ χ hρ hχ _ _ ε).mp hgap)

/-- Any solver in larger simplex dimensions yields a solver on the hard core
with exactly the same query count and success probability. -/
theorem exists_core_algorithm {m n M N T : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hM : m ≤ M) (hN : n ≤ N) {Seed : Type u} [MeasurableSpace Seed]
    (alg : Algorithm M N T Seed) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (ε : ℝ) (hsolve : Solves alg ν .simplexSimplex ε) :
    ∃ core : Algorithm m n T Seed, Solves core ν .simplexSimplex ε :=
  ⟨duplicateAlgorithm alg (coreProjection hm hM) (coreProjection hn hN),
    duplicateAlgorithm_solves alg ν _ _ (coreProjection_surjective hm hM)
      (coreProjection_surjective hn hN) ε hsolve⟩

end DimensionExtension
end
end Matvec
