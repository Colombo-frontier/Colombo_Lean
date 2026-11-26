import Bilevel.TransportAuxiliaryFramePrior
import Bilevel.TransportAuxiliaryFrameObservation
import Bilevel.SourceObserverBudget

/-! Same-run auxiliary query and terminal projection control under the
original network/auxiliary prior. No regularity event, conditional Haar
law, or projection-probability premise is supplied by the caller. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
universe u v
namespace Bilevel.TransportAuxiliaryFrame
open EuclideanGaussian ProjectionPosterior TransportControllerMachine
set_option autoImplicit false

variable {C : Type u} {S : Type v} [MeasurableSpace C] [MeasurableSpace S]
  {n D k T B : ℕ}

def originalInitial (initial : C × TransportNetwork.Latent n D → S)
    (p : C × TransportNetworkAuxiliary.Sample n D (k+1)) :
    State (C × TransportNetwork.Latent n D) S (k+1) T D :=
  ((p.1,p.2.1),(initial (p.1,p.2.1),initialStore (k+1) T D))

def OriginalProjectionGood (P : Schedule (k+1) T)
    (A : Driver (C × TransportNetwork.Latent n D) S (k+1) T D B)
    (hT : T+1 ≤ D) (i : Fin (k+1)) (hB : 0 < B) (N : ℕ)
    (initial : C × TransportNetwork.Latent n D → S) (cap : ℝ)
    (p : C × TransportNetworkAuxiliary.Sample n D (k+1)) : Prop :=
  ProjectionGood P A i hB N (otherColumns hT i (fun l => p.2.2 (i.succAbove l)))
    (originalColumns hT p.2) (originalInitial initial p) cap

theorem original_projection_failure (ρ : Measure C) [IsProbabilityMeasure ρ]
    (P : Schedule (k+1) T) (A : Driver (C × TransportNetwork.Latent n D) S (k+1) T D B)
    (hT : T+1 ≤ D) (i : Fin (k+1)) (hB : 0 < B) (N r : ℕ)
    (initial : C × TransportNetwork.Latent n D → S) (hi : Measurable initial)
    (b : ℝ) (hb : 0 < b) (hb2 : b ≤ 2)
    (hdim : (2*(N*B)+1)+(N*B)+(r+1) ≤ D)
    (hcap : ((N*B:ℕ):ℝ)*(((2*(N*B)+1:ℕ):ℝ)*b) ≤ 1/2) :
    (ρ.prod (TransportNetworkAuxiliary.law n D (k+1)))
      {p | ¬OriginalProjectionGood P A hT i hB N initial (2*((2*(N*B)+1:ℕ):ℝ)*b) p} ≤
      ((2*(N*B)+1:ℕ):ℝ≥0∞)*GenieProtocol.failurePerQuery (T+1) r b := by
  let L := selectedBatchRules P A i hB
  let start := selectedInitial hT i initial
  have hs : Measurable start := selectedInitial_measurable hT i initial hi
  have hp := auxiliary_observer_general ρ hT i (SourceFrameActions.compileRules L)
    (fun c => (start c,false)) (hs.prodMk measurable_const) 0 b hb hb2 hdim hcap
  refine (measure_mono ?_).trans hp
  intro p hbad hgood
  have hh := SourceFrameActions.compiled_source_observed L
    (2*((2*(N*B)+1:ℕ):ℝ)*b) (N*B) (N*B) 0
    (start (IndependentFrame.auxiliaryExpose hT i p).1,(⊥,∅))
    (IndependentFrame.auxiliaryExpose hT i p).2 le_rfl hgood
  exact hbad (sourceObserved_projectionGood P A i hB N
    (otherColumns hT i (fun l => p.2.2 (i.succAbove l)))
    (originalColumns hT p.2) (originalInitial initial p) _ hh)

theorem ProjectionGood.mono (P : Schedule (k+1) T)
    (A : Driver (C × TransportNetwork.Latent n D) S (k+1) T D B)
    (i : Fin (k+1)) (hB : 0 < B) (N : ℕ) (V U : Columns (k+1) T D)
    (s : State (C × TransportNetwork.Latent n D) S (k+1) T D) {a b : ℝ} (hab : a ≤ b)
    (h : ProjectionGood P A i hB N V U s a) : ProjectionGood P A i hB N V U s b := by
  exact ⟨fun j hj col hc => (h.1 j hj col hc).trans hab,fun col hc => (h.2 col hc).trans hab⟩

theorem original_projection_failure_of_budget (ρ : Measure C) [IsProbabilityMeasure ρ]
    (P : Schedule (k+1) T) (A : Driver (C × TransportNetwork.Latent n D) S (k+1) T D B)
    (hT : T+1 ≤ D) (i : Fin (k+1)) (hB : 0 < B) (N r : ℕ)
    (initial : C × TransportNetwork.Latent n D → S) (hi : Measurable initial)
    (b cap δ : ℝ) (hb : 0 < b) (hb2 : b ≤ 2)
    (hdim : (2*(N*B)+1)+(N*B)+(r+1) ≤ D)
    (hcap : ((N*B:ℕ):ℝ)*(((2*(N*B)+1:ℕ):ℝ)*b) ≤ 1/2)
    (he : 2*((2*(N*B)+1:ℕ):ℝ)*b ≤ cap)
    (hprob : ((2*(N*B)+1:ℕ):ℝ≥0∞)*GenieProtocol.failurePerQuery (T+1) r b = ENNReal.ofReal (δ/2)) :
    (ρ.prod (TransportNetworkAuxiliary.law n D (k+1)))
      {p | ¬OriginalProjectionGood P A hT i hB N initial cap p} ≤ ENNReal.ofReal (δ/2) := by
  have hp := original_projection_failure ρ P A hT i hB N r initial hi b hb hb2 hdim hcap
  rw [hprob] at hp
  refine (measure_mono ?_).trans hp
  intro p hbad hgood
  exact hbad (ProjectionGood.mono P A i hB N _ _ _ he hgood)

theorem exists_projection_dimension (D₀ N B T : ℕ) (δ cap : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hc : 0 < cap) :
    ∃ D r : ℕ, ∃ b : ℝ, D₀ ≤ D ∧ T+1 ≤ D ∧ (2*(N*B)+1)+(N*B)+(r+1) ≤ D ∧
      0 < r ∧ 0 < b ∧ b ≤ 2 ∧ ((N*B:ℕ):ℝ)*(((2*(N*B)+1:ℕ):ℝ)*b) ≤ 1/2 ∧
      2*((2*(N*B)+1:ℕ):ℝ)*b ≤ cap ∧
      ((2*(N*B)+1:ℕ):ℝ≥0∞)*GenieProtocol.failurePerQuery (T+1) r b = ENNReal.ofReal (δ/2) :=
  SourceObserverBudget.exists_dimension D₀ (2*(N*B)+1) (N*B) (T+1)
    (by omega) (by omega) δ cap hδ hδ1 hc

end Bilevel.TransportAuxiliaryFrame
