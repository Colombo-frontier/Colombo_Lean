import Bilevel.ChiSourceHierarchyHaar
import Bilevel.ChiSourceObserverDimension
import Mathlib.MeasureTheory.Function.Floor

/-! The public dimension is selected once, after all source scales and
the positive energy cap, before running any capped experiment. It covers
the entire expected-query proof's range of horizons and all source levels. -/
noncomputable section
open scoped ENNReal
namespace Bilevel.ChiHierarchyHaar
open ChiHierarchyIndex ChiHierarchyExecution ChiTreeProgress ChiRecursive ChiCurvatureSchedule ChiExtensionCalibration ChiBoundedChain

def sourceHorizon (counts : ℕ → ℕ) (J : ℕ) (p : ℝ) : ℕ :=
  ⌈(capacity counts (J+1) 0:ℕ)/(16*p)⌉₊

theorem sourceHorizon_bound (counts : ℕ → ℕ) (J : ℕ) (p : ℝ) :
    (capacity counts (J+1) 0:ℕ)/(16*p)≤(sourceHorizon counts J p:ℝ) := Nat.le_ceil _

theorem sourceHorizon_contains (counts : ℕ → ℕ) (J : ℕ) (p : ℝ) (n : ℕ)
    (hn : (n:ℝ)≤(capacity counts (J+1) 0:ℕ)/(16*p)) : n≤sourceHorizon counts J p :=
  Nat.cast_le.mp (hn.trans (sourceHorizon_bound counts J p))

theorem exists_uniform_source_dimension (macroN J queries : ℕ) {cn T : ℝ}
    (hcn : 0≤cn) (hT : 1≤T) (η Kg p cap : ℝ) (hc : 0<cap) :
    let counts := actualCounts macroN cn η T Kg
    let N := sourceHorizon counts J p
    ∃ D r : ℕ,∃ b : ℝ,
      sourceDimension macroN cn η T Kg≤D ∧
      (∀ j,sourceChainIndex cn (sourceRatio T j) (resolution η Kg j)+1≤D) ∧
      (∀ i : FrameIndex counts J,chainSize i+1≤D) ∧
      (2*(N*batchSize counts J queries)+1)+(N*batchSize counts J queries)+(r+1)≤D ∧
      0<r ∧ 0<b ∧ b≤2 ∧
      ((N*batchSize counts J queries:ℕ):ℝ)*(((2*(N*batchSize counts J queries)+1:ℕ):ℝ)*b)≤1/2 ∧
      2*((2*(N*batchSize counts J queries)+1:ℕ):ℝ)*b≤cap ∧
      ((2*(N*batchSize counts J queries)+1:ℕ):ℝ≥0∞)*
        GenieProtocol.failurePerQuery (totalColumns counts J) r b=1/8 := by
  dsimp only
  obtain ⟨D,r,b,hD,hAll,hdim,hr,hb,hb2,hproduct,henergy,hprob⟩ :=
    exists_source_observer_dimension (actualCounts macroN cn η T Kg) J queries
      (sourceHorizon (actualCounts macroN cn η T Kg) J p) (sourceDimension macroN cn η T Kg) cap hc
  exact ⟨D,r,b,hD,fun j => (actualCounts_inner_bound macroN hcn hT η Kg j).trans hD,
    hAll,hdim,hr,hb,hb2,hproduct,henergy,hprob⟩

end Bilevel.ChiHierarchyHaar
