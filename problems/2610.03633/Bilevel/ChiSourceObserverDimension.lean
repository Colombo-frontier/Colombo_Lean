import Bilevel.ChiSourceJointObserver

/-! A finite ambient dimension for the actual conservative source compiler.
All constants here affect only the public ambient dimension. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
universe u
namespace Bilevel.ChiHierarchyHaar
open ChiHierarchyIndex ChiHierarchyExecution EuclideanGaussian TransportControllerMachine

theorem exists_source_observer_dimension (counts : ℕ → ℕ) (J m N D₀ : ℕ)
    (cap : ℝ) (hc : 0<cap) :
    ∃ D r : ℕ, ∃ b : ℝ, D₀≤D ∧
      (∀ i : FrameIndex counts J,chainSize i+1≤D) ∧
      (2*(N*batchSize counts J m)+1)+(N*batchSize counts J m)+(r+1)≤D ∧
      0<r ∧ 0<b ∧ b≤2 ∧
      ((N*batchSize counts J m:ℕ):ℝ)*(((2*(N*batchSize counts J m)+1:ℕ):ℝ)*b)≤1/2 ∧
      2*((2*(N*batchSize counts J m)+1:ℕ):ℝ)*b≤cap ∧
      ((2*(N*batchSize counts J m)+1:ℕ):ℝ≥0∞)*
        GenieProtocol.failurePerQuery (totalColumns counts J) r b=1/8 := by
  obtain ⟨D,r,b,hD₀,hT,hdim,hr,hb,hb2,hcap,henergy,hprob⟩ :=
    SourceObserverBudget.exists_dimension D₀ (2*(N*batchSize counts J m)+1) (N*batchSize counts J m)
      (totalColumns counts J) (by omega) (totalColumns_pos counts J) (1/4) cap
      (by norm_num) (by norm_num) hc
  refine ⟨D,r,b,hD₀,fun i => (chainSize_le_totalColumns counts J i).trans hT,hdim,hr,hb,hb2,hcap,henergy,?_⟩
  simpa only [show ((1:ℝ)/4)/2=1/8 by norm_num,ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<8),
    ENNReal.ofReal_one,ENNReal.ofReal_ofNat] using hprob

theorem joint_observer_target {C : Type*} [MeasurableSpace C] (ρ : Measure C) [IsProbabilityMeasure ρ]
    {counts : ℕ → ℕ} {J D k N R r : ℕ} {H : Memory.{u}}
    (e : FrameIndex counts J ≃ Fin (k+1))
    (hD : ∀ i : FrameIndex counts J,chainSize i+1≤D)
    (L : ∀ i : FrameIndex counts J,OrdinaryFrame.Rules H D (chainSize i+1))
    (initial : ∀ _ : FrameIndex counts J,IndependentFrame.Context C D k → H)
    (hi : ∀ i,Measurable (initial i))
    (t : ℕ) (b cap : ℝ) (hb : 0<b) (hb2 : b≤2) (hdim : (2*N+1)+R+(r+1)≤D)
    (hcap : (R:ℝ)*(((2*N+1:ℕ):ℝ)*b)≤1/2) (henergy : 2*((2*N+1:ℕ):ℝ)*b≤cap) :
    (ρ.prod (law counts J D)) {p | ∃ i : FrameIndex counts J,
      ¬OrdinaryFrame.Observed (L i) cap N R t
        (initial i (sourceExpose e hD i p).1,(⊥,∅)) (sourceExpose e hD i p).2} ≤
      ((2*N+1:ℕ):ℝ≥0∞)*GenieProtocol.failurePerQuery (totalColumns counts J) r b := by
  refine (measure_mono ?_).trans (joint_observer_failure ρ e hD L initial hi t b hb hb2 hdim hcap)
  rintro p ⟨i,hi⟩
  exact ⟨i,fun h => hi (OrdinaryFrame.observed_mono (L i) henergy N R t _ _ h)⟩

end Bilevel.ChiHierarchyHaar
