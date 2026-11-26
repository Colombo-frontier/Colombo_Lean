import Bilevel.ChiSelectedFrameBatchRun
import Bilevel.ChiSelectedFramePrior

/-! Actual finite source-Haar probability for a selected-frame policy.
Complementary full frames are independent context. The enlarged query
budget is explicit and counts genie insertions, not source oracle calls. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
universe u
namespace Bilevel.ChiHierarchyHaar
open ChiHierarchyIndex EuclideanGaussian ProjectionPosterior TransportControllerMachine RawGenieBorel

theorem source_policy_failure {C : Type*} [MeasurableSpace C] (ρ : Measure C) [IsProbabilityMeasure ρ]
    {counts : ℕ → ℕ} {J D k M R r : ℕ} {H : Memory.{u}}
    (e : FrameIndex counts J ≃ Fin (k+1))
    (hD : ∀ i : FrameIndex counts J, chainSize i+1≤D) (i : FrameIndex counts J)
    (P : Policy D (chainSize i+1) H M R)
    (initial : IndependentFrame.Context C D k → H) (hi : Measurable initial)
    (b : ℝ) (hb : 0<b) (hb2 : b≤2) (hdim : M+R+(r+1)≤D)
    (hcap : (R:ℝ)*((M:ℝ)*b)≤1/2) :
    (ρ.prod (law counts J D)) {s | ¬RawGenieProtocol.Safe
      (ProjectionEnergy.envelope ((M:ℝ)*b) R)
      (compile P (initial (sourceExpose e hD i s).1)) ⊥ ∅ (sourceExpose e hD i s).2}≤
      (M:ℝ≥0∞)*GenieProtocol.failurePerQuery (chainSize i+1) r b := by
  let ν := ρ.prod (Measure.pi (fun _ : Fin k => OrthogonalHaar.law D))
  letI : IsProbabilityMeasure ν := inferInstanceAs (IsProbabilityMeasure
    (ρ.prod (Measure.pi (fun _ : Fin k => OrthogonalHaar.law D))))
  have hp := randomized_unsafe_probability (hD i) P initial hi ν b hb hb2 hdim hcap
  have hm := (hi.prodMap measurable_id) (initial_unsafe_measurable P
    (ProjectionEnergy.envelope ((M:ℝ)*b) R))
  have he := (sourceExpose_preserving ρ e hD i).measure_preimage hm.nullMeasurableSet
  change (ρ.prod (law counts J D)) {s | ¬RawGenieProtocol.Safe
      (ProjectionEnergy.envelope ((M:ℝ)*b) R)
      (compile P (initial (sourceExpose e hD i s).1)) ⊥ ∅ (sourceExpose e hD i s).2} = _ at he
  rw [he]
  exact hp

theorem source_observer {C : Type*} [MeasurableSpace C] (ρ : Measure C) [IsProbabilityMeasure ρ]
    {counts : ℕ → ℕ} {J D k N R r : ℕ} {H : Memory.{u}}
    (e : FrameIndex counts J ≃ Fin (k+1))
    (hD : ∀ i : FrameIndex counts J, chainSize i+1≤D) (i : FrameIndex counts J)
    (L : OrdinaryFrame.Rules H D (chainSize i+1))
    (initial : IndependentFrame.Context C D k → H) (hi : Measurable initial)
    (t : ℕ) (b : ℝ) (hb : 0<b) (hb2 : b≤2) (hdim : (2*N+1)+R+(r+1)≤D)
    (hcap : (R:ℝ)*(((2*N+1:ℕ):ℝ)*b)≤1/2) :
    (ρ.prod (law counts J D)) {s | ¬OrdinaryFrame.Observed L (2*((2*N+1:ℕ):ℝ)*b)
      N R t (initial (sourceExpose e hD i s).1,(⊥,∅)) (sourceExpose e hD i s).2}≤
      ((2*N+1:ℕ):ℝ≥0∞)*GenieProtocol.failurePerQuery (chainSize i+1) r b := by
  have hd' : OrdinaryFrame.queryCount N+R+(r+1)≤D := by
    simpa only [OrdinaryFrame.queryCount_eq] using hdim
  have hc' : (R:ℝ)*((OrdinaryFrame.queryCount N:ℝ)*b)≤1/2 := by
    simpa only [OrdinaryFrame.queryCount_eq] using hcap
  have hp := source_policy_failure ρ e hD i (OrdinaryFrame.policy L N R t) initial hi b hb hb2 hd' hc'
  have he := GenieProtocol.envelope_twice (OrdinaryFrame.queryCount N) R b hb.le hc'
  have hh : (ρ.prod (law counts J D)) {s | ¬OrdinaryFrame.Observed L
      (2*(OrdinaryFrame.queryCount N:ℝ)*b) N R t
      (initial (sourceExpose e hD i s).1,(⊥,∅)) (sourceExpose e hD i s).2}≤
      (OrdinaryFrame.queryCount N:ℝ≥0∞)*GenieProtocol.failurePerQuery (chainSize i+1) r b := by
    refine (measure_mono ?_).trans hp
    intro s hbad hsafe
    exact hbad (OrdinaryFrame.observed_mono L he N R t _ _
      (OrdinaryFrame.safe_observed L _ N R t _ _ hsafe))
  simpa only [OrdinaryFrame.queryCount_eq] using hh

end Bilevel.ChiHierarchyHaar
