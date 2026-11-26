import Bilevel.TransportAuxiliaryFrameObserver

/-! A measurable same-prior event controlling every auxiliary frame.
The proof uses only the selected independent-frame observer and a finite
union bound, with no independence assumption between failure events. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
universe u v
namespace Bilevel.TransportAuxiliaryFrame
open EuclideanGaussian ProjectionPosterior TransportControllerMachine
set_option autoImplicit false
variable {C : Type u} {S : Type v} [MeasurableSpace C] [MeasurableSpace S]
  {n D k T B : ℕ}

def OriginalObserved (P : Schedule (k+1) T)
    (A : Driver (C × TransportNetwork.Latent n D) S (k+1) T D B)
    (hT : T+1 ≤ D) (i : Fin (k+1)) (hB : 0 < B) (N : ℕ)
    (initial : C × TransportNetwork.Latent n D → S) (cap : ℝ)
    (p : C × TransportNetworkAuxiliary.Sample n D (k+1)) : Prop :=
  OrdinaryFrame.Observed (SourceFrameActions.compileRules (selectedBatchRules P A i hB))
    cap (N*B) (N*B) 0
    ((selectedInitial hT i initial (IndependentFrame.auxiliaryExpose hT i p).1,false),(⊥,∅))
    (IndependentFrame.auxiliaryExpose hT i p).2

theorem originalObserved_measurable (ρ : Measure C) [IsProbabilityMeasure ρ]
    (P : Schedule (k+1) T) (A : Driver (C × TransportNetwork.Latent n D) S (k+1) T D B)
    (hT : T+1 ≤ D) (i : Fin (k+1)) (hB : 0 < B) (N : ℕ)
    (initial : C × TransportNetwork.Latent n D → S) (hi : Measurable initial) (cap : ℝ) :
    MeasurableSet {p | OriginalObserved P A hT i hB N initial cap p} := by
  have he := (IndependentFrame.auxiliaryExpose_preserving (n:=n) ρ hT i).measurable
  let start := fun p : C × TransportNetworkAuxiliary.Sample n D (k+1) =>
    ((selectedInitial hT i initial (IndependentFrame.auxiliaryExpose hT i p).1,false),
      ((⊥ : Submodule ℝ (Space D)),(∅ : Set (Fin (T+1)))))
  have hs : OrdinaryFrame.BorelState
      (H:=SourceFrameActions.Marked (SelectedMemory (C × TransportNetwork.Latent n D) S (k+1) T D)) start := by
    refine ⟨?_,?_,fun _ => MeasurableSet.empty⟩
    · exact ((selectedInitial_measurable hT i initial hi).comp
        (measurable_fst.comp he)).prodMk measurable_const
    · change Measurable (fun _ : C × TransportNetworkAuxiliary.Sample n D (k+1) =>
        ProjectionStore.ofSubspace D (⊥ : Submodule ℝ (Space D)))
      exact measurable_const
  exact OrdinaryFrame.observed_measurable
    (SourceFrameActions.compileRules (selectedBatchRules P A i hB)) cap (N*B) (N*B) 0 start hs
      (fun p => (IndependentFrame.auxiliaryExpose hT i p).2) (measurable_snd.comp he)

theorem originalObserved_projectionGood (P : Schedule (k+1) T)
    (A : Driver (C × TransportNetwork.Latent n D) S (k+1) T D B)
    (hT : T+1 ≤ D) (i : Fin (k+1)) (hB : 0 < B) (N : ℕ)
    (initial : C × TransportNetwork.Latent n D → S) (cap : ℝ)
    (p : C × TransportNetworkAuxiliary.Sample n D (k+1))
    (h : OriginalObserved P A hT i hB N initial cap p) :
    OriginalProjectionGood P A hT i hB N initial cap p := by
  have hh := SourceFrameActions.compiled_source_observed (selectedBatchRules P A i hB)
    cap (N*B) (N*B) 0
    (selectedInitial hT i initial (IndependentFrame.auxiliaryExpose hT i p).1,(⊥,∅))
    (IndependentFrame.auxiliaryExpose hT i p).2 le_rfl h
  exact sourceObserved_projectionGood P A i hB N _ _ _ cap hh

theorem originalObserved_failure (ρ : Measure C) [IsProbabilityMeasure ρ]
    (P : Schedule (k+1) T) (A : Driver (C × TransportNetwork.Latent n D) S (k+1) T D B)
    (hT : T+1 ≤ D) (i : Fin (k+1)) (hB : 0 < B) (N r : ℕ)
    (initial : C × TransportNetwork.Latent n D → S) (hi : Measurable initial)
    (b : ℝ) (hb : 0 < b) (hb2 : b ≤ 2)
    (hdim : (2*(N*B)+1)+(N*B)+(r+1) ≤ D)
    (hcap : ((N*B:ℕ):ℝ)*(((2*(N*B)+1:ℕ):ℝ)*b) ≤ 1/2) :
    (ρ.prod (TransportNetworkAuxiliary.law n D (k+1)))
      {p | ¬OriginalObserved P A hT i hB N initial (2*((2*(N*B)+1:ℕ):ℝ)*b) p} ≤
      ((2*(N*B)+1:ℕ):ℝ≥0∞)*GenieProtocol.failurePerQuery (T+1) r b :=
  auxiliary_observer_general ρ hT i (SourceFrameActions.compileRules (selectedBatchRules P A i hB))
    (fun c => (selectedInitial hT i initial c,false))
    ((selectedInitial_measurable hT i initial hi).prodMk measurable_const) 0 b hb hb2 hdim hcap

theorem allObserved_measurable (ρ : Measure C) [IsProbabilityMeasure ρ]
    (P : Schedule (k+1) T) (A : Driver (C × TransportNetwork.Latent n D) S (k+1) T D B)
    (hT : T+1 ≤ D) (hB : 0 < B) (N : ℕ)
    (initial : C × TransportNetwork.Latent n D → S) (hi : Measurable initial) (cap : ℝ) :
    MeasurableSet {p | ∀ i, OriginalObserved P A hT i hB N initial cap p} := by
  convert MeasurableSet.iInter (fun i => originalObserved_measurable ρ P A hT i hB N initial hi cap) using 1
  ext p
  simp only [Set.mem_iInter,Set.mem_setOf_eq]

theorem allObserved_failure (ρ : Measure C) [IsProbabilityMeasure ρ]
    (P : Schedule (k+1) T) (A : Driver (C × TransportNetwork.Latent n D) S (k+1) T D B)
    (hT : T+1 ≤ D) (hB : 0 < B) (N r : ℕ)
    (initial : C × TransportNetwork.Latent n D → S) (hi : Measurable initial)
    (b : ℝ) (hb : 0 < b) (hb2 : b ≤ 2)
    (hdim : (2*(N*B)+1)+(N*B)+(r+1) ≤ D)
    (hcap : ((N*B:ℕ):ℝ)*(((2*(N*B)+1:ℕ):ℝ)*b) ≤ 1/2) :
    (ρ.prod (TransportNetworkAuxiliary.law n D (k+1)))
      {p | ¬∀ i, OriginalObserved P A hT i hB N initial (2*((2*(N*B)+1:ℕ):ℝ)*b) p} ≤
      ((k+1:ℕ):ℝ≥0∞)*(((2*(N*B)+1:ℕ):ℝ≥0∞)*GenieProtocol.failurePerQuery (T+1) r b) := by
  classical
  have he : {p : C × TransportNetworkAuxiliary.Sample n D (k+1) |
      ¬∀ i, OriginalObserved P A hT i hB N initial (2*((2*(N*B)+1:ℕ):ℝ)*b) p} =
      ⋃ i, {p | ¬OriginalObserved P A hT i hB N initial (2*((2*(N*B)+1:ℕ):ℝ)*b) p} := by
    ext p
    simp only [Set.mem_setOf_eq,Set.mem_iUnion,not_forall]
  rw [he]
  calc
    _ ≤ ∑' i, (ρ.prod (TransportNetworkAuxiliary.law n D (k+1)))
        {p | ¬OriginalObserved P A hT i hB N initial (2*((2*(N*B)+1:ℕ):ℝ)*b) p} := measure_iUnion_le _
    _ ≤ ∑' _i : Fin (k+1), ((2*(N*B)+1:ℕ):ℝ≥0∞)*GenieProtocol.failurePerQuery (T+1) r b :=
      ENNReal.tsum_le_tsum (fun i => originalObserved_failure ρ P A hT i hB N r initial hi b hb hb2 hdim hcap)
    _ = _ := by simp

end Bilevel.TransportAuxiliaryFrame
