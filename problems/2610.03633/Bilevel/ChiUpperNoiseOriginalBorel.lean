import Bilevel.ChiOriginalBorelHaar
import Bilevel.ChiFullDisclosureFormula
import Bilevel.ChiUpperNoiseBorelReply

/-! The original direct upper-noise family is jointly Borel in the frame,
query, and coin. Complete columns are used only to represent the instance,
not as the algorithm's disclosed store. -/
noncomputable section
set_option maxHeartbeats 500000
open MeasureTheory
namespace Bilevel.ChiUpperNoise
open ChiPrefixEvaluation ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry
variable {E F I : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

def completeCore (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F) (ρ R : ℕ → ℝ)
    (data : HierarchyData M D) : Queries E (Blocks m F) → ℝ :=
  fun q => virtualJointOuter m M ν D ρ R 0 1 (M.n+1) (fullCounts D) data.1 data.2 (queryProjection q)

def completeInactive (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F) (ρ R : ℕ → ℝ)
    (data : HierarchyData M D) (q : Queries E (Blocks m F)) : ℝ :=
  completeCore m M ν D ρ R data q-
    virtualOuterLeaf m M D (M.n+1) (fullCounts D) data.1 data.2 (signalLeaf D ((D 0 []).width/16)) 0 (queryProjection q)

theorem completeCore_frame_eq (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F) (ρ R : ℕ → ℝ)
    (UM : I → Space M.n →ₗᵢ[ℝ] E) (U : I → ∀ j P,Space (D j P).n →ₗᵢ[ℝ] F) (i : I) :
    completeCore m M ν D ρ R (frameData M D UM U i)=
      fullCore m (reframeNode M (UM i)) ν (reframeGeometry D (U i)) ρ R := by
  funext q
  exact virtualJointOuter_frame_eq m M ν D ρ R 0 1 UM U i (queryProjection q)

theorem completeInactive_frame_eq (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F) (ρ R : ℕ → ℝ)
    (UM : I → Space M.n →ₗᵢ[ℝ] E) (U : I → ∀ j P,Space (D j P).n →ₗᵢ[ℝ] F) (i : I) :
    completeInactive m M ν D ρ R (frameData M D UM U i)=
      fullInactiveCore m (reframeNode M (UM i)) ν (reframeGeometry D (U i)) ρ R := by
  funext q
  unfold completeInactive
  rw [completeCore_frame_eq]
  apply congrArg₂ (fun a b : ℝ => a-b) rfl
  rw [← virtualOuterLeaf_reframe (D:=D) (U:=U i) (m:=m) (M:=M) (UM:=UM i)]
  exact virtualOuterSignal_full m (reframeNode M (UM i)) (reframeGeometry D (U i)) 0
    ((D 0 []).width/16) (queryProjection q)

omit [CompleteSpace E] [CompleteSpace F] in
theorem completeCore_continuous (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F) (ρ R : ℕ → ℝ) :
    Continuous (Function.uncurry (completeCore m M ν D ρ R)) := by
  let args : HierarchyData M D × Queries E (Blocks m F) → HierarchyData M D × Joint E (Blocks m F) :=
    fun p => (p.1,queryProjection p.2)
  have ha : Continuous args :=
    continuous_fst.prodMk ((queryProjection (E:=E) (U:=Blocks m F)).continuous.comp continuous_snd)
  have hs := virtualJointOuter_continuous m M ν D ρ R 0 1 (M.n+1) (fullCounts D)
  have hc := hs.comp ha
  exact hc

omit [CompleteSpace E] [CompleteSpace F] in
theorem completeInactive_continuous (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F) (ρ R : ℕ → ℝ) :
    Continuous (Function.uncurry (completeInactive m M ν D ρ R)) := by
  let args : HierarchyData M D × Queries E (Blocks m F) → HierarchyData M D × Joint E (Blocks m F) :=
    fun p => (p.1,queryProjection p.2)
  have ha : Continuous args :=
    continuous_fst.prodMk ((queryProjection (E:=E) (U:=Blocks m F)).continuous.comp continuous_snd)
  have hs := virtualOuterLeaf_continuous m M D (M.n+1) (fullCounts D) (signalLeaf D ((D 0 []).width/16))
    (fun j P => (ChiFine.signalResidual_contDiff (D j P).n (D j P).ell (D j P).width _).continuous) 0
  have hc := hs.comp ha
  have hdiff := (completeCore_continuous m M ν D ρ R).sub hc
  exact hdiff

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] [MeasurableSpace I]

theorem originalPair_measurable (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F) (ρ R : ℕ → ℝ)
    [MeasurableSpace (Queries E (Blocks m F))] [BorelSpace (Queries E (Blocks m F))]
    (UM : I → Space M.n →ₗᵢ[ℝ] E) (U : I → ∀ j P,Space (D j P).n →ₗᵢ[ℝ] F)
    (hdata : Measurable (frameData M D UM U)) (g : Queries E (Blocks m F) → ℝ)
    (hg : Continuous g) (π : ℝ) :
    Measurable (fun p : I × (Queries E (Blocks m F) × Bool) =>
      (ChiConservative.sampleGradient (fullCore m (reframeNode M (UM p.1)) ν (reframeGeometry D (U p.1)) ρ R)
        (fullInactiveCore m (reframeNode M (UM p.1)) ν (reframeGeometry D (U p.1)) ρ R) π p.2.2 p.2.1,
        gradient g p.2.1)) := by
  let Q := Queries E (Blocks m F)
  letI : SecondCountableTopology (Blocks m F) := inferInstance
  letI : SecondCountableTopology (Joint E (Blocks m F)) := inferInstance
  letI : SecondCountableTopology Q := inferInstance
  letI : BorelSpace (HierarchyData M D) := inferInstance
  letI : SecondCountableTopology (HierarchyData M D) := inferInstance
  have hc := twoStorePair_measurable (completeCore m M ν D ρ R) (completeInactive m M ν D ρ R) g π
    (completeCore_continuous m M ν D ρ R) (completeInactive_continuous m M ν D ρ R) hg
  have hargs : Measurable (fun p : I × (Q × Bool) =>
      (p.2.1,(frameData M D UM U p.1,(frameData M D UM U p.1,p.2.2)))) :=
    measurable_snd.fst.prodMk ((hdata.comp measurable_fst).prodMk
      ((hdata.comp measurable_fst).prodMk measurable_snd.snd))
  have hh := hc.comp hargs
  convert hh using 1
  funext p
  simp only [Function.comp_apply,twoStorePair,ChiConservative.sampleGradient,completeCore_frame_eq,completeInactive_frame_eq]

end Bilevel.ChiUpperNoise
