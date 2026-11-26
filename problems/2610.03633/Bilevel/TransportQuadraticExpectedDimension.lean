import Bilevel.TransportQuadraticExpectedProperty
import Bilevel.ChiUpperNoisePublicWitness
import Bilevel.ChiSourceHierarchyHaar

/-! One public ambient dimension for the complete expected-query argument.
The dimension accommodates the actual source frames and every truncation
cap before any private algorithm or random orientation is chosen. -/
noncomputable section
namespace Bilevel.TransportHierarchy
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiExtensionCalibration
  EndpointTransportResponse ChiUpperNoise ChiHierarchyHaar
set_option autoImplicit false
set_option maxHeartbeats 1200000

theorem exists_quadratic_expected_dimension (macroN n : ℕ) (sc : Scale)
    (cn η Kg δ c K ε CR ζ Km : ℝ) (weight : ℕ → ℝ) (rad R : ℕ → ℝ)
    (hl : 0<sc.curvature) (hw : 0<sc.width) (hcn : 0≤cn) (hη : 0<η) (hKg : 0<Kg)
    (hres : ∀ j,resolution η Kg j≤1) (hweight : ∀ j,0<weight j)
    (hCR : 0<CR) (hζ : 0<ζ) (hKm : 0<Km) (hε : 0<ε) :
    ∃ D : ℕ,
    ∃ hdim : ∀ j,sourceChainIndex cn 1 (resolution η Kg j)+1≤D,
    ∃ hAll : ∀ i : FrameIndex (sourceCounts macroN cn (fun _ => 1) (resolution η Kg)) 0,chainSize i+1≤D,
    ∃ hT : capacity (sourceCounts macroN cn (fun _ => 1) (resolution η Kg)) 1 0≤D,
    QuadraticBarrier macroN n D cn (fun _ => 1) (resolution η Kg) hdim hAll hT sc weight ζ CR Km rad R K ε →
    QuadraticExpectedProperty macroN n D cn (fun _ => 1) (resolution η Kg) hdim hAll hT sc weight ζ CR Km rad R K ε δ c := by
  let counts := sourceCounts macroN cn (fun _ => 1) (resolution η Kg)
  have hrespos := base_resolution_positive hη hKg
  have hcap := (sourcePublicCap_positive macroN 0 sc (fun _ => 1) (resolution η Kg) weight
    CR ζ Km sc.width hl hw (fun _ => le_rfl) hrespos hweight hCR hζ hKm hw).1
  obtain ⟨D,hD,hT,hA,hbudget⟩ := exists_quadratic_dimension (sourceDimension macroN cn η 1 Kg)
    macroN n ((n+1)*capacity counts 1 0) cn (fun _ => 1) (resolution η Kg) sc weight CR ζ Km sc.width (1/8)
    hcap (by norm_num) (by norm_num)
  have hdim : ∀ j,sourceChainIndex cn 1 (resolution η Kg j)+1≤D := by
    intro j
    have hh := (actualCounts_inner_bound macroN hcn (by norm_num : (1:ℝ)≤1) η Kg j).trans hD
    simpa only [actualCounts,sourceRatio_one,sourceCounts] using hh
  have ha := actualCounts_all_bound macroN 0 hcn (by norm_num : (1:ℝ)≤1) η Kg
  dsimp only [actualCounts] at ha
  rw [sourceRatio_one] at ha
  have hAll : ∀ i : FrameIndex counts 0,chainSize i+1≤D := fun i => (ha i).trans hD
  refine ⟨D,hdim,hAll,hT,?_⟩
  intro hbarrier
  exact quadratic_expected_property macroN n D cn (fun _ => 1) (resolution η Kg) hdim hAll hT sc weight ζ CR Km rad R K ε
    hA hl hw (fun _ => le_rfl) hrespos hres hweight hζ hCR hKm δ c sc.width hw hε hbudget hbarrier

end Bilevel.TransportHierarchy
