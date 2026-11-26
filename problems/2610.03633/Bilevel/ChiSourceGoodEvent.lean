import Bilevel.ChiSourceObserverDimension
import Bilevel.ChiSourceTerminalObserver

/-! One measurable same-run source observer event. It supplies every
original-call fresh-space energy bound and every selected-frame terminal
readout bound, with total failure controlled on the original Haar prior. -/
noncomputable section
open MeasureTheory
open scoped ENNReal RealInnerProductSpace
universe u
namespace Bilevel.ChiHierarchyHaar
open ChiHierarchyIndex ChiHierarchyExecution BorelAdaptive EuclideanGaussian

variable {C : Type*} {S : Type u} {Q O Y : Type*} [MeasurableSpace C] [MeasurableSpace S]
  [MeasurableSpace Q] [MeasurableSpace O] [MeasurableSpace Y]
variable (counts : ℕ → ℕ) (J D m : ℕ)
  (hD : ∀ i : FrameIndex counts J,chainSize i+1≤D) (A : Program S Q O Y)
  (evaluate : Q → Store counts J (Space D) → Store counts J (Space D) → Bool → O)
  (he : Measurable (fun p : Q × (Store counts J (Space D) × (Store counts J (Space D) × Bool)) =>
    evaluate p.1 p.2.1 p.2.2.1 p.2.2.2))
  (queries : Fin m → Q × Store counts J (Space D) → Space D) (hq : ∀ l, Measurable (queries l))
  (output : FrameIndex counts J → Y → Space D) (ho : ∀ i,Measurable (output i))
  (initial : C → S) (draws : C → ℕ → Bool)

def sourceGood (N : ℕ) (cap : ℝ) (p : C × Orientations counts J D) : Prop :=
  ∀ i : FrameIndex counts J,
    OrdinaryFrame.Observed
      (SourceFrameActions.compileRules (batchedFrameRules counts J D m i A evaluate he queries hq (output i) (ho i)))
      cap (N*batchSize counts J m) (N*batchSize counts J m) 0
      (observerInitial (succEnumeration counts J) hD i initial draws
        (sourceExpose (succEnumeration counts J) hD i p).1,(⊥,∅))
      (sourceExpose (succEnumeration counts J) hD i p).2

theorem sourceGood_measurable (hi : Measurable initial) (hd : Measurable draws) (N : ℕ) (cap : ℝ) :
    MeasurableSet {p | sourceGood counts J D m hD A evaluate he queries hq output ho initial draws N cap p} :=
  joint_observed_measurable (succEnumeration counts J) hD
    (fun i => SourceFrameActions.compileRules (batchedFrameRules counts J D m i A evaluate he queries hq (output i) (ho i)))
    (fun i => observerInitial (succEnumeration counts J) hD i initial draws)
    (fun i => observerInitial_measurable _ hD i initial hi draws hd) _ _ _ _

theorem sourceGood_failure (ρ : Measure C) [IsProbabilityMeasure ρ]
    (hi : Measurable initial) (hd : Measurable draws) (N r : ℕ) (b cap : ℝ)
    (hb : 0<b) (hb2 : b≤2)
    (hdim : (2*(N*batchSize counts J m)+1)+(N*batchSize counts J m)+(r+1)≤D)
    (hcap : ((N*batchSize counts J m:ℕ):ℝ)*(((2*(N*batchSize counts J m)+1:ℕ):ℝ)*b)≤1/2)
    (henergy : 2*((2*(N*batchSize counts J m)+1:ℕ):ℝ)*b≤cap) :
    (ρ.prod (law counts J D)) {p | ¬sourceGood counts J D m hD A evaluate he queries hq output ho initial draws N cap p} ≤
      ((2*(N*batchSize counts J m)+1:ℕ):ℝ≥0∞)*GenieProtocol.failurePerQuery (totalColumns counts J) r b := by
  have h := joint_observer_target ρ (succEnumeration counts J) hD
    (fun i => SourceFrameActions.compileRules (batchedFrameRules counts J D m i A evaluate he queries hq (output i) (ho i)))
    (fun i => observerInitial (succEnumeration counts J) hD i initial draws)
    (fun i => observerInitial_measurable _ hD i initial hi draws hd) 0 b cap hb hb2 hdim hcap henergy
  simpa only [sourceGood,not_forall] using h

omit [MeasurableSpace C] in
theorem sourceGood_call (N : ℕ) (cap : ℝ) (p : C × Orientations counts J D)
    (hgood : sourceGood counts J D m hD A evaluate he queries hq output ho initial draws N cap p)
    (t : ℕ) (ht : t<N) (i : FrameIndex counts J) :
    let U := columns hD p.2
    let z := run counts J A evaluate U (initial p.1) (draws p.1) t
    GenieProtocol.BoundedEnergy
      (sharedKnown counts J D z.2.1 U (Submodule.span ℝ (Set.range (fun l => queries l (A.query z.1,z.2)))))
      (prefixSet (retained counts J z.2.1 i)) (U i) cap := by
  let e := succEnumeration counts J
  let C' := otherColumns e hD i (sourceExpose e hD i p).1.2
  have hC : ∀ j, j≠i → C' j=columns hD p.2 j := otherColumns_agree e hD i p.2
  have hs := SourceFrameActions.compiled_source_observed
    (batchedFrameRules counts J D m i A evaluate he queries hq (output i) (ho i)) cap
    (N*batchSize counts J m) (N*batchSize counts J m) 0
    (((C',draws p.1),initialState counts J (initial p.1)),(⊥,∅)) (columns hD p.2 i) le_rfl (hgood i)
  exact call_shared_energy counts J D m i A evaluate he queries hq (output i) (ho i)
    C' (columns hD p.2) hC (initial p.1) (draws p.1) N t ht cap hs

omit [MeasurableSpace C] in
theorem sourceGood_terminal (N : ℕ) (cap : ℝ) (hcap : 0≤cap) (p : C × Orientations counts J D)
    (hgood : sourceGood counts J D m hD A evaluate he queries hq output ho initial draws N cap p)
    (i : FrameIndex counts J) (k : Fin (chainSize i+1))
    (hk : retained counts J (run counts J A evaluate (columns hD p.2) (initial p.1) (draws p.1) N).2.1 i≤k.val) :
    let y := A.output (run counts J A evaluate (columns hD p.2) (initial p.1) (draws p.1) N).1
    |⟪columns hD p.2 i k,output i y⟫|≤Real.sqrt cap*‖output i y‖ := by
  let e := succEnumeration counts J
  exact actual_terminal_bound counts J D m i A evaluate he queries hq (output i) (ho i)
    (otherColumns e hD i (sourceExpose e hD i p).1.2) (columns hD p.2)
    (otherColumns_agree e hD i p.2) (initial p.1) (draws p.1) N (N*batchSize counts J m)
    le_rfl cap hcap (hgood i) k hk

end Bilevel.ChiHierarchyHaar
