import Geode.PartialOracle
import Geode.ResistingOracle
import Geode.UpperAlgorithm
import Geode.StrictLocalization

/-! Fixed-instance failure and matching minimax complexity for deterministic
algorithms whose internal computation is allowed to diverge. -/
namespace Geode.Lorentz

open Geode.OracleReplay
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

abbrev PartialFirstOrderAlgorithm (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] := PartialStoppingAlgorithm (Point E) (FirstOrderReply E)

def PartialGuarantees (o : Point E) (R L ε : ℝ) (N : ℕ)
    (A : PartialFirstOrderAlgorithm E) : Prop :=
  ∀ f : Point E → ℝ, AdmissibleObjective o R L f →
    ∀ O : Point E → FirstOrderReply E, LegalOracle f O →
      ∃ history output,
        partialRun A (fixedResponder O) N [] = .finished history output ∧
        ∀ p : Point E, (∀ y, f p ≤ f y) → f output - f p ≤ ε * L * R

def PartialFeasibleBudget (o : Point E) (R L ε : ℝ) (N : ℕ) : Prop :=
  ∃ A : PartialFirstOrderAlgorithm E, PartialGuarantees o R L ε N A

theorem PartialGuarantees.totalize {o : Point E} {R L ε : ℝ} {N : ℕ}
    {A : PartialFirstOrderAlgorithm E} (hA : PartialGuarantees o R L ε N A)
    (default : Point E) : Guarantees o R L ε N (A.totalize default) := by
  intro f hf O hO
  obtain ⟨h, output, hrun, hgap⟩ := hA f hf O hO
  exact ⟨h, output, partial_finished_totalizes A default (fixedResponder O) N [] h output hrun,
    hgap⟩

theorem Guarantees.toPartial {o : Point E} {R L ε : ℝ} {N : ℕ}
    {A : FirstOrderAlgorithm E} (hA : Guarantees o R L ε N A) :
    PartialGuarantees o R L ε N A.toPartial := by
  intro f hf O hO
  obtain ⟨h, output, hrun, hgap⟩ := hA f hf O hO
  exact ⟨h, output, total_finished_embeds A (fixedResponder O) N [] h output hrun, hgap⟩

/-- Allowing internal divergence does not alter any feasible query budget:
a guaranteed algorithm cannot stall on an admissible instance. -/
theorem partialFeasibleBudget_iff (o : Point E) (R L ε : ℝ) (N : ℕ) :
    PartialFeasibleBudget o R L ε N ↔ FeasibleBudget o R L ε N := by
  constructor
  · rintro ⟨A, hA⟩
    exact ⟨A.totalize o, hA.totalize o⟩
  · rintro ⟨A, hA⟩
    exact ⟨A.toPartial, hA.toPartial⟩

noncomputable def partialQueryComplexity (o : Point E) (R L ε : ℝ) : ℝ≥0∞ :=
  ⨅ (N : ℕ) (_ : PartialFeasibleBudget o R L ε N), (N : ℝ≥0∞)

theorem partialQueryComplexity_eq (o : Point E) (R L ε : ℝ) :
    partialQueryComplexity o R L ε = queryComplexity o R L ε := by
  simp only [partialQueryComplexity, queryComplexity, partialFeasibleBudget_iff]

noncomputable def partialUniformComplexity (R L ε : ℝ) : ℝ≥0∞ :=
  ⨆ (d : ℕ) (_ : 2 ≤ d), partialQueryComplexity (origin : HyperbolicSpace d) R L ε

theorem partialUniformComplexity_eq (R L ε : ℝ) :
    partialUniformComplexity R L ε = uniformComplexity R L ε := by
  simp only [partialUniformComplexity, uniformComplexity, dimensionComplexity,
    partialQueryComplexity_eq]

/-- The explicit upper algorithm remains valid in the partial decision model. -/
theorem projectedAlgorithm_partial_guarantees (o : Point E) {R L ε : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hε : 0 < ε) :
    PartialGuarantees o R L ε (upperQueryBudget R ε)
      (projectedAlgorithm o R L ε hR.le).toPartial :=
  (projectedAlgorithm_guarantees o hR hL hε).toPartial

def PartialStrictGuarantees (o : Point E) (R L ε : ℝ) (N : ℕ)
    (A : PartialFirstOrderAlgorithm E) : Prop :=
  ∀ f : Point E → ℝ, StrictAdmissibleObjective o R L f →
    ∀ O : Point E → FirstOrderReply E, LegalOracle f O →
      ∃ history output,
        partialRun A (fixedResponder O) N [] = .finished history output ∧
        ∀ p : Point E, (∀ y, f p ≤ f y) → f output - f p ≤ ε * L * R

def PartialStrictFeasibleBudget (o : Point E) (R L ε : ℝ) (N : ℕ) : Prop :=
  ∃ A : PartialFirstOrderAlgorithm E, PartialStrictGuarantees o R L ε N A

theorem PartialStrictGuarantees.totalize {o : Point E} {R L ε : ℝ} {N : ℕ}
    {A : PartialFirstOrderAlgorithm E} (hA : PartialStrictGuarantees o R L ε N A)
    (default : Point E) : StrictGuarantees o R L ε N (A.totalize default) := by
  intro f hf O hO
  obtain ⟨h, output, hrun, hgap⟩ := hA f hf O hO
  exact ⟨h, output, partial_finished_totalizes A default (fixedResponder O) N [] h output hrun,
    hgap⟩

theorem StrictGuarantees.toPartial {o : Point E} {R L ε : ℝ} {N : ℕ}
    {A : FirstOrderAlgorithm E} (hA : StrictGuarantees o R L ε N A) :
    PartialStrictGuarantees o R L ε N A.toPartial := by
  intro f hf O hO
  obtain ⟨h, output, hrun, hgap⟩ := hA f hf O hO
  exact ⟨h, output, total_finished_embeds A (fixedResponder O) N [] h output hrun, hgap⟩

theorem partialStrictFeasibleBudget_iff (o : Point E) (R L ε : ℝ) (N : ℕ) :
    PartialStrictFeasibleBudget o R L ε N ↔ StrictFeasibleBudget o R L ε N := by
  constructor
  · rintro ⟨A, hA⟩
    exact ⟨A.totalize o, hA.totalize o⟩
  · rintro ⟨A, hA⟩
    exact ⟨A.toPartial, hA.toPartial⟩

noncomputable def partialStrictQueryComplexity (o : Point E) (R L ε : ℝ) : ℝ≥0∞ :=
  ⨅ (N : ℕ) (_ : PartialStrictFeasibleBudget o R L ε N), (N : ℝ≥0∞)

theorem partialStrictQueryComplexity_eq (o : Point E) (R L ε : ℝ) :
    partialStrictQueryComplexity o R L ε = strictQueryComplexity o R L ε := by
  simp only [partialStrictQueryComplexity, strictQueryComplexity, partialStrictFeasibleBudget_iff]

noncomputable def partialStrictUniformComplexity (R L ε : ℝ) : ℝ≥0∞ :=
  ⨆ (d : ℕ) (_ : 2 ≤ d), partialStrictQueryComplexity (origin : HyperbolicSpace d) R L ε

theorem partialStrictUniformComplexity_eq (R L ε : ℝ) :
    partialStrictUniformComplexity R L ε = strictUniformComplexity R L ε := by
  simp only [partialStrictUniformComplexity, strictUniformComplexity, strictDimensionComplexity,
    partialStrictQueryComplexity_eq]

variable [FiniteDimensional ℝ E]

/-- A single fixed admissible objective and globally legal oracle defeat every
partial algorithm. Internal stalling, budget exhaustion, and inaccurate output
are all covered; the minimizer is unique and lies on the localization sphere. -/
theorem precise_failure_witness_partial (o : Point E) {R L ε : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hε : 0 < ε) (hεmax : ε ≤ 1 / 64)
    (hdim : Geode.queryHorizon R ε + 3 ≤ Module.finrank ℝ (Ambient E))
    (A : PartialFirstOrderAlgorithm E) :
    ∃ (f : Point E → ℝ) (O : Point E → FirstOrderReply E) (p : Point E),
      AdmissibleObjective o R L f ∧ LegalOracle f O ∧
      (∀ y, (∀ z, f y ≤ f z) ↔ y = p) ∧ f p = 0 ∧ dist o p = R ∧
      PartialRunFails (fun output => 2 * ε * L * R ≤ f output - f p)
        (partialRun A (fixedResponder O) (Geode.queryHorizon R ε) []) := by
  obtain ⟨f, O, p, hf, hO, hmin, hzero, hp, hfail⟩ :=
    precise_failure_witness o hR hL hε hεmax hdim (A.totalize o)
  exact ⟨f, O, p, hf, hO, hmin, hzero, hp,
    totalized_failure_transfers A o (fixedResponder O) (Geode.queryHorizon R ε) [] _ hfail⟩

theorem partial_uniform_lower {R L ε : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hε : 0 < ε) (hεmax : ε ≤ 1 / 64) :
    ENNReal.ofReal (Geode.curvatureFactor R / (260 * ε ^ 2)) ≤
      partialUniformComplexity R L ε := by
  rw [partialUniformComplexity_eq]
  apply uniform_lower_of_failure_witness hR hL hε hεmax
  exact horizon_failure_witness origin hR hL hε hεmax
    (by rw [ambient_finrank_query_dimension])

/-- The manuscript's matching rate, including algorithms that can diverge
during internal computation between oracle calls. -/
theorem partial_matching_complexity {R L ε : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hε : 0 < ε) (hεmax : ε ≤ 1 / 64) :
    ENNReal.ofReal (Geode.curvatureFactor R / (260 * ε ^ 2)) ≤
        partialUniformComplexity R L ε ∧
      partialUniformComplexity R L ε ≤ (⌈3 * Geode.curvatureFactor R / ε ^ 2⌉₊ : ℝ≥0∞) := by
  refine ⟨partial_uniform_lower hR hL hε hεmax, ?_⟩
  rw [partialUniformComplexity_eq]
  exact uniformComplexity_upper_three hR hL hε

/-- The open-ball localization corollary also permits internal divergence. -/
theorem partial_strict_localization {R L ε : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hε : 0 < ε) (hεmax : ε ≤ 1 / 64) :
    ENNReal.ofReal (3 * Geode.curvatureFactor R / (1040 * ε ^ 2)) ≤
        partialStrictUniformComplexity R L ε ∧
      partialStrictUniformComplexity R L ε ≤ (⌈3 * Geode.curvatureFactor R / ε ^ 2⌉₊ : ℝ≥0∞) := by
  rw [partialStrictUniformComplexity_eq]
  refine ⟨?_, strictUniformComplexity_upper hR hL hε⟩
  apply strictUniformComplexity_lower_of_failure_witness hR hL hε hεmax
  exact horizon_failure_witness origin (by linarith) hL hε hεmax
    (by rw [ambient_finrank_query_dimension])

end Geode.Lorentz
