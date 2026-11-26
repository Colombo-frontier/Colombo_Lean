import Bilevel.ChiSourcePublicFine
import Bilevel.ChiSourceQueryVectors

/-! One public ambient dimension pays the actual source's smallest blind
width for every truncation horizon used by the expected-call argument.
The cap and horizon are chosen before the dimension and contain no frame. -/
noncomputable section
open scoped ENNReal
namespace Bilevel.ChiHierarchyHaar
open ChiHierarchyIndex ChiHierarchyExecution ChiTreeProgress ChiBoundedChain ChiRecursive
  ChiCurvatureSchedule ChiExtensionCalibration

theorem exists_calibrated_source_dimension (macroN J : ℕ)
    (sc : Scale) (cn T η Kg c v p CR ζ Km : ℝ) (weight : ℕ → ℝ)
    (hl : 0<sc.curvature) (hw : 0<sc.width) (hcn : 0≤cn) (hT : 1≤T)
    (hη : 0<η) (hKg : 0<Kg) (hc : 0<c) (hv : 1≤v)
    (hweight : ∀ j,0<weight j) (hCR : 0<CR) (hζ : 0<ζ) (hKm : 0<Km) :
    let counts := actualCounts macroN cn η T Kg
    let N := sourceHorizon counts J p
    let τ := sourcePublicFinestWidth sc (sourceRatio T) (resolution η Kg) J c v
    let cap := sourcePublicCap macroN J sc (sourceRatio T) (resolution η Kg) weight CR ζ Km τ
    0<cap ∧ ∃ D r : ℕ,∃ b : ℝ,
      sourceDimension macroN cn η T Kg≤D ∧
      (∀ j,sourceChainIndex cn (sourceRatio T j) (resolution η Kg j)+1≤D) ∧
      (∀ i : FrameIndex counts J,chainSize i+1≤D) ∧
      (2*(N*batchSize counts J (queryVectorCount (J+1)))+1)+
        (N*batchSize counts J (queryVectorCount (J+1)))+(r+1)≤D ∧
      0<r ∧ 0<b ∧ b≤2 ∧
      ((N*batchSize counts J (queryVectorCount (J+1)):ℕ):ℝ)*
        (((2*(N*batchSize counts J (queryVectorCount (J+1)))+1:ℕ):ℝ)*b)≤1/2 ∧
      2*((2*(N*batchSize counts J (queryVectorCount (J+1)))+1:ℕ):ℝ)*b≤cap ∧
      ((2*(N*batchSize counts J (queryVectorCount (J+1)))+1:ℕ):ℝ≥0∞)*
        GenieProtocol.failurePerQuery (totalColumns counts J) r b=1/8 := by
  have hres := base_resolution_positive hη hKg
  have hτ := sourcePublicFinestWidth_pos sc (sourceRatio T) (resolution η Kg) J c v
    hl hw (sourceRatio_ge_one hT) hres hc hv
  have hcap := (sourcePublicCap_positive macroN J sc (sourceRatio T) (resolution η Kg) weight
    CR ζ Km (sourcePublicFinestWidth sc (sourceRatio T) (resolution η Kg) J c v)
    hl hw (sourceRatio_ge_one hT) hres hweight hCR hζ hKm hτ).1
  exact ⟨hcap,exists_uniform_source_dimension macroN J (queryVectorCount (J+1)) hcn hT η Kg p _ hcap⟩

end Bilevel.ChiHierarchyHaar
