import Bilevel.ChiSourceCallObserver
import Bilevel.ChiSelectedFrameInitialization

/-! Actual source-call projection failure on the original finite hierarchy
prior. The source computation is executed, not assumed to be zero-respecting. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
universe u
namespace Bilevel.ChiHierarchyHaar
open ChiHierarchyIndex ChiHierarchyExecution BorelAdaptive EuclideanGaussian ProjectionPosterior

theorem sourceExpose_measurable {C : Type*} [MeasurableSpace C] {counts : ℕ → ℕ} {J D k : ℕ}
    (e : FrameIndex counts J ≃ Fin (k+1)) (hD : ∀ i : FrameIndex counts J,chainSize i+1≤D)
    (i : FrameIndex counts J) : Measurable (sourceExpose (C:=C) e hD i) := by
  have ho : Measurable (fun p : C × Orientations counts J D =>
      fun l => p.2 (e.symm ((e i).succAbove l))) := by
    apply measurable_pi_lambda
    intro l
    exact (measurable_pi_apply _).comp measurable_snd
  exact (measurable_fst.prodMk ho).prodMk
    (((measurable_pi_apply i).comp (columns_measurable hD)).comp measurable_snd)

theorem source_observed_measurable {C : Type*} [MeasurableSpace C] {counts : ℕ → ℕ} {J D k : ℕ}
    {H : TransportControllerMachine.Memory.{u}}
    (e : FrameIndex counts J ≃ Fin (k+1)) (hD : ∀ i : FrameIndex counts J,chainSize i+1≤D)
    (i : FrameIndex counts J) (L : OrdinaryFrame.Rules H D (chainSize i+1))
    (initial : IndependentFrame.Context C D k → H) (hi : Measurable initial)
    (N R t : ℕ) (cap : ℝ) :
    MeasurableSet {p : C × Orientations counts J D | OrdinaryFrame.Observed L cap N R t
      (initial (sourceExpose e hD i p).1,(⊥,∅)) (sourceExpose e hD i p).2} := by
  let F := IndependentFrame.Context C D k × Frame D (chainSize i+1)
  have hs : OrdinaryFrame.BorelState (d:=D) (T:=chainSize i+1) (H:=H)
      (fun p : F => (initial p.1,(⊥,∅))) := by
    refine ⟨hi.comp measurable_fst,?_,fun _ => MeasurableSet.empty⟩
    change Measurable (fun _ : F => ProjectionStore.ofSubspace D (⊥ : Submodule ℝ (Space D)))
    exact measurable_const
  have hm := OrdinaryFrame.observed_measurable L cap N R t _ hs Prod.snd measurable_snd
  exact hm.preimage (sourceExpose_measurable e hD i)

variable {C : Type*} {S : Type u} {Q O Y : Type*} [MeasurableSpace C] [MeasurableSpace S]
  [MeasurableSpace Q] [MeasurableSpace O] [MeasurableSpace Y]

theorem actual_call_failure (ρ : Measure C) [IsProbabilityMeasure ρ]
    {counts : ℕ → ℕ} {J D k : ℕ} (e : FrameIndex counts J ≃ Fin (k+1))
    (hD : ∀ i : FrameIndex counts J,chainSize i+1≤D) (i : FrameIndex counts J)
    (A : Program S Q O Y)
    (evaluate : Q → Store counts J (Space D) → Store counts J (Space D) → Bool → O)
    (he : Measurable (fun p : Q × (Store counts J (Space D) × (Store counts J (Space D) × Bool)) =>
      evaluate p.1 p.2.1 p.2.2.1 p.2.2.2))
    (m : ℕ) (queries : Fin m → Q × Store counts J (Space D) → Space D) (hq : ∀ l, Measurable (queries l))
    (output : Y → Space D) (ho : Measurable output)
    (initial : C → S) (hi : Measurable initial) (draws : C → ℕ → Bool) (hd : Measurable draws)
    (N R r : ℕ) (hR : N*batchSize counts J m≤R)
    (b : ℝ) (hb : 0<b) (hb2 : b≤2)
    (hdim : (2*(N*batchSize counts J m)+1)+R+(r+1)≤D)
    (hcap : (R:ℝ)*(((2*(N*batchSize counts J m)+1:ℕ):ℝ)*b)≤1/2) :
    (ρ.prod (law counts J D)) {p | ∃ t<N,
      let U := columns hD p.2
      let z := run counts J A evaluate U (initial p.1) (draws p.1) t
      ¬GenieProtocol.BoundedEnergy
        (sharedKnown counts J D z.2.1 U (Submodule.span ℝ (Set.range (fun l => queries l (A.query z.1,z.2)))))
        (prefixSet (retained counts J z.2.1 i)) (U i)
        (2*((2*(N*batchSize counts J m)+1:ℕ):ℝ)*b)} ≤
      ((2*(N*batchSize counts J m)+1:ℕ):ℝ≥0∞)*GenieProtocol.failurePerQuery (chainSize i+1) r b := by
  let L := batchedFrameRules counts J D m i A evaluate he queries hq output ho
  have hp := source_observer ρ e hD i (SourceFrameActions.compileRules L)
    (observerInitial e hD i initial draws) (observerInitial_measurable e hD i initial hi draws hd)
    0 b hb hb2 hdim hcap
  refine (measure_mono ?_).trans hp
  intro p hbad hgood
  obtain ⟨t,ht,hbad⟩ := hbad
  have hs := SourceFrameActions.compiled_source_observed L _ (N*batchSize counts J m) R 0
    (((otherColumns e hD i (sourceExpose e hD i p).1.2,draws p.1),initialState counts J (initial p.1)),(⊥,∅))
    (columns hD p.2 i) hR hgood
  exact hbad (call_shared_energy counts J D m i A evaluate he queries hq output ho
    (otherColumns e hD i (sourceExpose e hD i p).1.2) (columns hD p.2)
    (otherColumns_agree e hD i p.2) (initial p.1) (draws p.1) N t ht _ hs)

end Bilevel.ChiHierarchyHaar
