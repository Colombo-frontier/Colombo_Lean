import Bilevel.ChiUpperNoisePrefixValues
import Bilevel.ChiUpperNoiseBorelReply
import Bilevel.ChiFiniteVirtualState
import Bilevel.ChiFiniteVirtualReply

/-! Actual finite-store evaluator for the direct upper-noise family. Its
scalars use disclosed columns and public node numbers, then are pulled
back to every block of the original query. -/
noncomputable section
set_option maxHeartbeats 400000
open MeasureTheory
namespace Bilevel.ChiUpperNoise
open ChiPrefixEvaluation ChiHierarchyIndex ChiHierarchyExecution ChiBoundedChain ChiRecursive ChiCarrier
  PrimitiveGeometry PartialLegendre
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def stateDirectCore (m : ℕ) (M : ChiRecursive.Node E) (ν : ℝ) (D : Geometry E)
    (ρ R : ℕ → ℝ) (rM : ℕ → ℕ) (r : ℕ → ℕ → List ℕ → ℕ)
    (p : VirtualState M D) : Queries E (Blocks m E) → ℝ :=
  stateUpperBase m M ν D 0 (ρ 0) (R 0) rM r p ∘ queryProjection

def stateDirectInactive (m : ℕ) (M : ChiRecursive.Node E) (ν : ℝ) (D : Geometry E)
    (ρ R : ℕ → ℝ) (rM : ℕ → ℕ) (r : ℕ → ℕ → List ℕ → ℕ)
    (p : VirtualState M D) : Queries E (Blocks m E) → ℝ :=
  virtualDirectInactive m M ν D ρ R (rM p.1) (r p.1) p.2.1 p.2.2 ∘ queryProjection

omit [CompleteSpace E] in
theorem stateDirectCore_continuous (m : ℕ) (M : ChiRecursive.Node E) (ν : ℝ) (D : Geometry E)
    (ρ R : ℕ → ℝ) (rM : ℕ → ℕ) (r : ℕ → ℕ → List ℕ → ℕ) :
    Continuous (Function.uncurry (stateDirectCore m M ν D ρ R rM r)) := by
  let args : VirtualState M D × Queries E (Blocks m E) → VirtualState M D × Joint E (Blocks m E) :=
    fun p => (p.1,queryProjection p.2)
  have ha : Continuous args :=
    continuous_fst.prodMk ((queryProjection (E:=E) (U:=Blocks m E)).continuous.comp continuous_snd)
  have hs := stateUpperBase_continuous m M ν D 0 (ρ 0) (R 0) rM r
  have h := hs.comp ha
  exact h

omit [CompleteSpace E] in
theorem virtualDirectInactive_continuous (m : ℕ) (M : ChiRecursive.Node E) (ν : ℝ) (D : Geometry E)
    (ρ R : ℕ → ℝ) (rM : ℕ) (r : ℕ → List ℕ → ℕ) :
    Continuous (fun p : HierarchyData M D × Joint E (Blocks m E) =>
      virtualDirectInactive m M ν D ρ R rM r p.1.1 p.1.2 p.2) :=
  (virtualUpperBase_continuous m M ν D 0 (ρ 0) (R 0) rM r).sub
    (virtualOuterLeaf_continuous m M D rM r (signalLeaf D ((D 0 []).width/16))
      (fun j I => (ChiFine.signalResidual_contDiff (D j I).n (D j I).ell (D j I).width _).continuous) 0)

omit [CompleteSpace E] in
theorem stateDirectInactive_continuous (m : ℕ) (M : ChiRecursive.Node E) (ν : ℝ) (D : Geometry E)
    (ρ R : ℕ → ℝ) (rM : ℕ → ℕ) (r : ℕ → ℕ → List ℕ → ℕ) :
    Continuous (Function.uncurry (stateDirectInactive m M ν D ρ R rM r)) := by
  have h : Continuous (fun p : ℕ × (HierarchyData M D × Joint E (Blocks m E)) =>
      virtualDirectInactive m M ν D ρ R (rM p.1) (r p.1) p.2.1.1 p.2.1.2 p.2.2) :=
    continuous_prod_of_discrete_left.mpr (fun q => virtualDirectInactive_continuous m M ν D ρ R (rM q) (r q))
  let args : VirtualState M D × Queries E (Blocks m E) → ℕ × (HierarchyData M D × Joint E (Blocks m E)) :=
    fun p => (p.1.1,(p.1.2,queryProjection p.2))
  have ha : Continuous args := continuous_fst.fst.prodMk
    (continuous_fst.snd.prodMk ((queryProjection (E:=E) (U:=Blocks m E)).continuous.comp continuous_snd))
  have hc := h.comp ha
  exact hc

def finiteDirectEvaluate (counts : ℕ → ℕ) (m : ℕ) (M : ChiRecursive.Node E) (ν : ℝ) (D : Geometry E)
    (hM : M.n=counts 0) (hD : ∀ j I,(D j I).n=counts (j+1)) (ρ R : ℕ → ℝ)
    (g : Queries E (Blocks m E) → ℝ) (π : ℝ) (q : Queries E (Blocks m E))
    (old new : Store counts 0 E) (coin : Bool) : Queries E (Blocks m E) × Queries E (Blocks m E) :=
  twoStorePair
    (stateDirectCore m M ν D ρ R (finiteMacroCounter counts 0) (canonicalCounter counts 0))
    (stateDirectInactive m M ν D ρ R (finiteMacroCounter counts 0) (canonicalCounter counts 0))
    g π q (finiteVirtualState counts 0 M D hM hD old) (finiteVirtualState counts 0 M D hM hD new) coin

omit [CompleteSpace E] in
theorem stateDirectCore_reframe (m : ℕ) (M : ChiRecursive.Node E) (ν : ℝ) (D : Geometry E)
    (UM : Space M.n →ₗᵢ[ℝ] E) (U : ∀ j I,Space (D j I).n →ₗᵢ[ℝ] E)
    (ρ R : ℕ → ℝ) (rM : ℕ → ℕ) (r : ℕ → ℕ → List ℕ → ℕ) (p : VirtualState M D) :
    stateDirectCore m (reframeNode M UM) ν (reframeGeometry D U) ρ R rM r p=
      stateDirectCore m M ν D ρ R rM r p := by
  unfold stateDirectCore
  rw [stateUpperBase_reframe]

omit [CompleteSpace E] in
theorem stateDirectInactive_reframe (m : ℕ) (M : ChiRecursive.Node E) (ν : ℝ) (D : Geometry E)
    (UM : Space M.n →ₗᵢ[ℝ] E) (U : ∀ j I,Space (D j I).n →ₗᵢ[ℝ] E)
    (ρ R : ℕ → ℝ) (rM : ℕ → ℕ) (r : ℕ → ℕ → List ℕ → ℕ) (p : VirtualState M D) :
    stateDirectInactive m (reframeNode M UM) ν (reframeGeometry D U) ρ R rM r p=
      stateDirectInactive m M ν D ρ R rM r p := by
  funext q
  unfold stateDirectInactive virtualDirectInactive
  dsimp only [Function.comp_apply]
  rw [virtualUpperBase_reframe]
  have hs : signalLeaf (reframeGeometry D U) ((reframeGeometry D U 0 []).width/16)=
      signalLeaf D ((D 0 []).width/16) := rfl
  rw [hs,virtualOuterLeaf_reframe]

theorem finiteDirectEvaluate_reframe (counts : ℕ → ℕ) (m : ℕ) (M : ChiRecursive.Node E) (ν : ℝ) (D : Geometry E)
    (hM : M.n=counts 0) (hD : ∀ j I,(D j I).n=counts (j+1))
    (UM : Space M.n →ₗᵢ[ℝ] E) (U : ∀ j I,Space (D j I).n →ₗᵢ[ℝ] E)
    (ρ R : ℕ → ℝ) (g : Queries E (Blocks m E) → ℝ) (π : ℝ)
    (q : Queries E (Blocks m E)) (old new : Store counts 0 E) (coin : Bool) :
    finiteDirectEvaluate counts m (reframeNode M UM) ν (reframeGeometry D U) hM hD ρ R g π q old new coin=
      finiteDirectEvaluate counts m M ν D hM hD ρ R g π q old new coin := by
  simp only [finiteDirectEvaluate,twoStorePair,finiteVirtualState_reframe,stateDirectCore_reframe,stateDirectInactive_reframe]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem finiteDirectEvaluate_measurable (counts : ℕ → ℕ) (m : ℕ) (M : ChiRecursive.Node E) (ν : ℝ) (D : Geometry E)
    (hM : M.n=counts 0) (hD : ∀ j I,(D j I).n=counts (j+1)) (ρ R : ℕ → ℝ)
    [MeasurableSpace (Queries E (Blocks m E))] [BorelSpace (Queries E (Blocks m E))]
    (g : Queries E (Blocks m E) → ℝ) (hg : Continuous g) (π : ℝ) :
    Measurable (fun p : Queries E (Blocks m E) × (Store counts 0 E × (Store counts 0 E × Bool)) =>
      finiteDirectEvaluate counts m M ν D hM hD ρ R g π p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let Q := Queries E (Blocks m E)
  letI : SecondCountableTopology (Blocks m E) := inferInstance
  letI : SecondCountableTopology (Joint E (Blocks m E)) := inferInstance
  letI : SecondCountableTopology Q := inferInstance
  letI : BorelSpace (VirtualState M D) := inferInstance
  letI : SecondCountableTopology (VirtualState M D) := inferInstance
  have hold := (finiteVirtualState_measurable counts 0 M D hM hD).comp
    (measurable_snd.fst : Measurable (fun p : Q × (Store counts 0 E × (Store counts 0 E × Bool)) => p.2.1))
  have hnew := (finiteVirtualState_measurable counts 0 M D hM hD).comp
    (measurable_snd.snd.fst : Measurable (fun p : Q × (Store counts 0 E × (Store counts 0 E × Bool)) => p.2.2.1))
  have hargs : Measurable (fun p : Q × (Store counts 0 E × (Store counts 0 E × Bool)) =>
      (p.1,(finiteVirtualState counts 0 M D hM hD p.2.1,
        (finiteVirtualState counts 0 M D hM hD p.2.2.1,p.2.2.2)))) :=
    measurable_fst.prodMk (hold.prodMk (hnew.prodMk measurable_snd.snd.snd))
  have hs := twoStorePair_measurable
    (stateDirectCore m M ν D ρ R (finiteMacroCounter counts 0) (canonicalCounter counts 0))
    (stateDirectInactive m M ν D ρ R (finiteMacroCounter counts 0) (canonicalCounter counts 0)) g π
    (stateDirectCore_continuous m M ν D ρ R (finiteMacroCounter counts 0) (canonicalCounter counts 0))
    (stateDirectInactive_continuous m M ν D ρ R (finiteMacroCounter counts 0) (canonicalCounter counts 0)) hg
  have hh := hs.comp hargs
  exact hh

end Bilevel.ChiUpperNoise
