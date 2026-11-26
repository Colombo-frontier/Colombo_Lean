import Bilevel.ChiUpperNoiseExpectedProperty

/-! One public dimension for the direct upper-noise expected-query theorem.
Only the deterministic calibrated macro barrier is supplied afterward. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace Bilevel.ChiHierarchyHaar
open ChiHierarchyIndex ChiHierarchyExecution ChiTreeProgress ChiBoundedChain ChiRecursive
  ChiOuter ChiCarrier ChiPrefixEvaluation ChiExtensionCalibration PrimitiveGeometry ChiUpperNoise
  PartialLegendre BorelAdaptive ChiCurvatureSchedule

theorem exists_upper_noise_expected_dimension (macroN : ℕ) (sc : Scale)
    (cn η Kg μ L K ε π CR ζ Km : ℝ) (weight : ℕ → ℝ)
    (hl : 0<sc.curvature) (hw : 0<sc.width) (hcn : 0≤cn) (hη : 0<η) (hKg : 0<Kg)
    (hres : ∀ j,resolution η Kg j≤1) (hweight : ∀ j,0<weight j)
    (hCR : 0<CR) (hζ : 0<ζ) (hKm : 0<Km) (hπ : 0<π) (hπ1 : π≤1) (hε : 0<ε) :
    ∃ dim : ℕ,
    ∃ hdim : ∀ j,sourceChainIndex cn 1 (resolution η Kg j)+1≤dim,
    ∃ hAll : ∀ i : FrameIndex (sourceCounts macroN cn (fun _ => 1) (resolution η Kg)) 0,chainSize i+1≤dim,
    UpperNoiseBarrier macroN dim cn (fun _ => 1) (resolution η Kg) hdim hAll sc weight ζ CR Km
      (sourcePublicRadialWeight sc (fun _ => 1) (resolution η Kg) weight ζ)
      (sourcePublicNodeRadius sc (fun _ => 1) (resolution η Kg) weight CR ζ) K ε →
    UpperNoiseExpectedProperty macroN dim cn (fun _ => 1) (resolution η Kg) hdim hAll sc weight ζ CR Km
      (sourcePublicRadialWeight sc (fun _ => 1) (resolution η Kg) weight ζ)
      (sourcePublicNodeRadius sc (fun _ => 1) (resolution η Kg) weight CR ζ) K ε μ L π hπ1 := by
  have hd := exists_upper_noise_source_dimension macroN sc cn η Kg π CR ζ Km weight
    hl hw hcn hη hKg hweight hCR hζ hKm
  dsimp only [actualCounts] at hd
  rw [sourceRatio_one] at hd
  obtain ⟨_,dim,r,b,_,hdim,hAll,hd,_,hb,hb2,hprod,henergy,hprob⟩ := hd
  refine ⟨dim,hdim,hAll,?_⟩
  intro hbarrier
  exact upper_noise_expected_property macroN dim cn (fun _ => 1) (resolution η Kg) hdim hAll
    sc weight ζ CR Km
    (sourcePublicRadialWeight sc (fun _ => 1) (resolution η Kg) weight ζ)
    (sourcePublicNodeRadius sc (fun _ => 1) (resolution η Kg) weight CR ζ) K ε
    hl hw (fun _ => le_rfl) (base_resolution_positive hη hKg) hres hweight hζ hCR hKm
    μ L π hπ hπ1 hε (sourceHorizon (sourceCounts macroN cn (fun _ => 1) (resolution η Kg)) 0 π) r b
    (sourceHorizon_bound _ 0 π) hb hb2 hd hprod henergy hprob.le hbarrier

end Bilevel.ChiHierarchyHaar
