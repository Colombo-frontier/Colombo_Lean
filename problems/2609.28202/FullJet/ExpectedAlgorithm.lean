import FullJet.StoppingAlgorithm
import FullJet.Capping
import FullJet.OracleComplexity

open MeasureTheory
open scoped ENNReal

namespace FullJet

namespace StoppingJetAlgorithm

variable {Ω E : Type} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E] {n p : ℕ}

/-- Measurability of the actual finite observations and finite-budget outputs. -/
def measurableOn (A : StoppingJetAlgorithm Ω E n p) (Δ L : ℝ) : Prop :=
  (∀ f, Admissible p n Δ L f → ∀ N, MeasurableSet {s | A.halt s (A.state f s N) = true}) ∧
    ∀ N, A.capped.measurableOn N Δ L

/-- The expected criterion uses actual stopping executions. Almost-sure
termination and integrability prevent nontermination or undefined integrals
from being counted as zero-cost successful runs. -/
structure ExpectedGuarantee (A : StoppingJetAlgorithm Ω E n p) (P : Measure Ω)
    (Δ L Q ε : ℝ) : Prop where
  measurable : A.measurableOn Δ L
  halts_ae : ∀ f, Admissible p n Δ L f → ∀ᵐ s ∂P, A.Halts f s
  cost_integrable : ∀ f, Admissible p n Δ L f → Integrable (fun s => (A.stopIndex f s : ℝ)) P
  gradient_integrable : ∀ f, Admissible p n Δ L f →
    Integrable (fun s => ‖fderiv ℝ (average f) (A.stoppedResult f s)‖) P
  cost_bound : ∀ f, Admissible p n Δ L f → ∫ s, (A.stopIndex f s : ℝ) ∂P ≤ Q
  gradient_bound : ∀ f, Admissible p n Δ L f →
    ∫ s, ‖fderiv ℝ (average f) (A.stoppedResult f s)‖ ∂P ≤ ε

/-- The bad event of the actual capped execution is contained, almost
surely, in the two Markov events for the original stopping execution. -/
theorem capped_failure_le (A : StoppingJetAlgorithm Ω E n p) (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Fin n → E → ℝ) (R ε δ : ℝ) (hR : 0 < R) (hε : 0 < ε) (hδ : 0 < δ)
    (hhalt : ∀ᵐ s ∂P, A.Halts f s)
    (hc : Integrable (fun s => (A.stopIndex f s : ℝ)) P)
    (hg : Integrable (fun s => ‖fderiv ℝ (average f) (A.stoppedResult f s)‖) P)
    (hcmean : ∫ s, (A.stopIndex f s : ℝ) ∂P ≤ R)
    (hgmean : ∫ s, ‖fderiv ℝ (average f) (A.stoppedResult f s)‖ ∂P ≤ ε) :
    P.real {s | ε / (δ / 2) <
      ‖fderiv ℝ (average f) (A.capped.result ⌈R / (δ / 2)⌉₊ f s)‖} ≤ δ := by
  have hb := capping_failure_le hc hg (fun s => Nat.cast_nonneg _) (fun s => norm_nonneg _)
    R ε δ hR hε hδ hcmean hgmean
  apply le_trans _ hb
  apply ENNReal.toReal_mono (measure_ne_top P _)
  apply measure_mono_ae
  filter_upwards [hhalt] with s hs
  intro hbad
  change ε / (δ / 2) < ‖fderiv ℝ (average f) (A.capped.result ⌈R / (δ / 2)⌉₊ f s)‖ at hbad
  by_cases ht : A.stopIndex f s ≤ ⌈R / (δ / 2)⌉₊
  · right
    exact (show ε / (δ / 2) < ‖fderiv ℝ (average f) (A.stoppedResult f s)‖ by
      simpa only [A.capped_result_eq_stoppedResult f s hs ht] using hbad).le
  · left
    have ht' : (⌈R / (δ / 2)⌉₊ : ℝ) ≤ A.stopIndex f s := by exact_mod_cast (by omega : ⌈R / (δ / 2)⌉₊ ≤ A.stopIndex f s)
    exact (Nat.le_ceil _).trans ht'

theorem ExpectedGuarantee.capped_succeeds {A : StoppingJetAlgorithm Ω E n p}
    {P : Measure Ω} [IsProbabilityMeasure P] {Δ L Q ε : ℝ}
    (hA : A.ExpectedGuarantee P Δ L Q ε) (R δ : ℝ) (hQR : Q ≤ R)
    (hR : 0 < R) (hε : 0 < ε) (hδ : 0 < δ) :
    A.capped.succeeds P ⌈R / (δ / 2)⌉₊ Δ L (ε / (δ / 2)) δ := by
  refine ⟨hA.measurable.2 _, ?_⟩
  intro f hf
  exact A.capped_failure_le P f R ε δ hR hε hδ (hA.halts_ae f hf)
    (hA.cost_integrable f hf) (hA.gradient_integrable f hf)
    ((hA.cost_bound f hf).trans hQR) (hA.gradient_bound f hf)

end StoppingJetAlgorithm

def UniformStoppingAlgorithm.expectedGuarantee {Ω : Type} [MeasurableSpace Ω] {n p : ℕ}
    (A : UniformStoppingAlgorithm Ω n p) (P : Measure Ω) (Δ L Q ε : ℝ) : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E],
    (A E).ExpectedGuarantee P Δ L Q ε

structure RandomizedStoppingMethod (n p : ℕ) where
  Seed : Type
  seedSpace : MeasurableSpace Seed
  law : @Measure Seed seedSpace
  probability : @IsProbabilityMeasure Seed seedSpace law
  algorithm : UniformStoppingAlgorithm Seed n p

def RandomizedStoppingMethod.expectedGuarantee {n p : ℕ} (M : RandomizedStoppingMethod n p)
    (Δ L Q ε : ℝ) : Prop := by
  letI := M.seedSpace
  exact M.algorithm.expectedGuarantee M.law Δ L Q ε

def RandomizedStoppingMethod.capped {n p : ℕ} (M : RandomizedStoppingMethod n p) : RandomizedJetMethod n p where
  Seed := M.Seed
  seedSpace := M.seedSpace
  law := M.law
  probability := M.probability
  algorithm := fun E _ _ _ => (M.algorithm E).capped

theorem RandomizedStoppingMethod.capped_succeeds {n p : ℕ} (M : RandomizedStoppingMethod n p)
    {Δ L Q ε : ℝ} (hM : M.expectedGuarantee Δ L Q ε) (R δ : ℝ) (hQR : Q ≤ R)
    (hR : 0 < R) (hε : 0 < ε) (hδ : 0 < δ) :
    M.capped.succeeds ⌈R / (δ / 2)⌉₊ Δ L (ε / (δ / 2)) δ := by
  letI := M.seedSpace
  letI := M.probability
  intro E _ _ _
  exact (hM E).capped_succeeds R δ hQR hR hε hδ

/-- Minimax expected query cost under the actual stopping-time and expected
gradient criterion, not under a supplied bound for a hypothetical restart. -/
noncomputable def expectedOracleComplexity (n p : ℕ) (Δ L ε : ℝ) : ℝ≥0∞ :=
  sInf {b | ∃ (Q : ℝ) (M : RandomizedStoppingMethod n p), 0 ≤ Q ∧ b = ENNReal.ofReal Q ∧
    M.expectedGuarantee Δ L Q ε}

theorem expectedOracleComplexity_le_of_method {n p : ℕ} (M : RandomizedStoppingMethod n p)
    (Δ L Q ε : ℝ) (hQ : 0 ≤ Q) (hM : M.expectedGuarantee Δ L Q ε) :
    expectedOracleComplexity n p Δ L ε ≤ ENNReal.ofReal Q :=
  sInf_le ⟨Q, M, hQ, rfl, hM⟩

end FullJet
