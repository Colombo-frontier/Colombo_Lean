import Bilevel.TransportPhysicalExpectedProperty
import Bilevel.ChiSourceHierarchyHaar
import Bilevel.ChiCanonicalPublicData

/-! One fixed public dimension accommodates all source frames and every
truncation cap before a private algorithm or random physical sample is chosen. -/
noncomputable section
namespace Bilevel.TransportHierarchy
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiCarrier ChiExtensionCalibration
  EndpointTransportResponse ChiHierarchyHaar PrimitiveGeometry ChiExtension
set_option autoImplicit false
set_option maxHeartbeats 1200000

theorem exists_physical_expected_dimension (macroN J n s : ℕ) (sc : Scale)
    (cn T η Kg K ε CR ζ Km : ℝ) (weight : ℕ → ℝ)
    (fine : ChiFine.Parameters) (ci ri : Fin J → Fin s) (fi : Fin s)
    (dn : ℝ) (normal : Normals s) (m δ c₀ cend : ℝ)
    (hJ : 0<J) (hl : 0<sc.curvature) (hw : 0<sc.width) (hcn : 0≤cn) (hT : 1≤T)
    (hη : 0<η) (hKg : 0<Kg) (hres : ∀ j,resolution η Kg j≤1) (hweight : ∀ j,0<weight j)
    (hCR : 0<CR) (hζ : 0<ζ) (hKm : 0<Km) (hε : 0<ε)
    (hℓ : fine.ℓ=sourcePublicEll sc (sourceRatio T) (resolution η Kg) J)
    (hβ : fine.β=sourcePublicWidth sc (sourceRatio T) (resolution η Kg) J)
    (hcomplete : ∀ (dim' : ℕ) (Q : Rotations n dim')
      (U : Space macroN →ₗᵢ[ℝ] Block dim')
      (V : ∀ j,List ℕ → Space (sourceChainIndex cn (sourceRatio T j) (resolution η Kg j)) →ₗᵢ[ℝ] Block dim'),
      let M' := ChiOuter.sourceMacroNode macroN sc Km U
      let G' := sourceGeometry sc (sourceRatio T) (resolution η Kg) weight 3 1 ζ cn CR V
      let rad' := fun j => weight j*(G' j []).nu
      let R' := fun j => (G' j []).radius
      ContDiff ℝ 3 (physicalHierarchyExtension Q M' G' fine J s ci ri fi rad' R' dn) ∧
      ∀ z,‖iteratedFDeriv ℝ 2 (physicalHierarchyExtension Q M' G' fine J s ci ri fi rad' R' dn) z‖≤(1:ℝ)/12) :
    let rad := sourcePublicRadialWeight sc (sourceRatio T) (resolution η Kg) weight ζ
    let R := sourcePublicNodeRadius sc (sourceRatio T) (resolution η Kg) weight CR ζ
    ∃ D : ℕ,
    ∃ hdim : ∀ j,sourceChainIndex cn (sourceRatio T j) (resolution η Kg j)+1≤D,
    ∃ hAll : ∀ i : FrameIndex (sourceCounts macroN cn (sourceRatio T) (resolution η Kg)) J,chainSize i+1≤D,
    ∃ hTerm : capacity (sourceCounts macroN cn (sourceRatio T) (resolution η Kg)) (J+1) 0≤D,
    ∃ hF : ∀ sample : PhysicalSample (sourceCounts macroN cn (sourceRatio T) (resolution η Kg)) J n D,
      LipschitzWith (⟨1/12,by norm_num⟩ : NNReal) (gradient (physicalOriginalPotential
        macroN J n D s cn (sourceRatio T) (resolution η Kg) hdim hAll hTerm sc weight 3 1 ζ CR Km fine ci ri fi rad R dn sample)),
    PhysicalBarrier macroN J n D cn (sourceRatio T) (resolution η Kg) hdim hAll hTerm
      sc weight 3 1 ζ CR Km (sc.curvature/24) rad R K ε →
    PhysicalExpectedProperty macroN J n D s cn (sourceRatio T) (resolution η Kg) hdim hAll hTerm
      sc weight 3 1 ζ CR Km (sc.curvature/24) fine ci ri fi rad R dn normal m δ c₀ cend hF K ε := by
  let counts := sourceCounts macroN cn (sourceRatio T) (resolution η Kg)
  let rad := sourcePublicRadialWeight sc (sourceRatio T) (resolution η Kg) weight ζ
  let R := sourcePublicNodeRadius sc (sourceRatio T) (resolution η Kg) weight CR ζ
  have hrespos := base_resolution_positive hη hKg
  have hratios := sourceRatio_ge_one hT
  have hcap := (sourcePublicCap_positive macroN J sc (sourceRatio T) (resolution η Kg) weight
    CR ζ Km sc.width hl hw hratios hrespos hweight hCR hζ hKm hw).1
  obtain ⟨D,hD,hTerm,hA,hbudget⟩ := exists_physical_dimension (sourceDimension macroN cn η T Kg)
    macroN J n ((n+1)*capacity counts (J+1) 0) cn (sourceRatio T) (resolution η Kg)
    sc weight CR ζ Km sc.width (1/8) hcap (by norm_num) (by norm_num)
  have hdim : ∀ j,sourceChainIndex cn (sourceRatio T j) (resolution η Kg j)+1≤D :=
    fun j => (actualCounts_inner_bound macroN hcn hT η Kg j).trans hD
  have hAll : ∀ i : FrameIndex counts J,chainSize i+1≤D :=
    fun i => (actualCounts_all_bound macroN J hcn hT η Kg i).trans hD
  have hcore (sample : PhysicalSample counts J n D) := physicalOriginalCore_hessian
    macroN J n D s cn (sourceRatio T) (resolution η Kg) hdim hAll hTerm sc weight 3 1 ζ CR Km
    fine ci ri fi rad R dn hcomplete sample (fun _ => rfl) (fun _ => rfl)
  have hF (sample : PhysicalSample counts J n D) :
      LipschitzWith (⟨1/12,by norm_num⟩ : NNReal) (gradient (physicalOriginalPotential
        macroN J n D s cn (sourceRatio T) (resolution η Kg) hdim hAll hTerm sc weight 3 1 ζ CR Km fine ci ri fi rad R dn sample)) :=
    physicalExtension_gradient_lipschitz (hcore sample).1 ⟨1/12,by norm_num⟩ (hcore sample).2
  refine ⟨D,hdim,hAll,hTerm,hF,?_⟩
  intro hbarrier
  exact physical_expected_property macroN J n D s cn (sourceRatio T) (resolution η Kg) hdim hAll hTerm
    sc weight 3 1 ζ CR Km (sc.curvature/24) fine ci ri fi rad R dn normal m δ c₀ cend hF K ε
    hcomplete (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => hℓ) (fun _ => hβ)
    hJ hl hw hratios hrespos hres hweight hζ hCR hKm hA sc.width hw hε hbudget hbarrier

end Bilevel.TransportHierarchy
