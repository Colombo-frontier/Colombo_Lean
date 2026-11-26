import Bilevel.ChiSourceCalibratedDimension

/-! A finite public dimension for the direct J=0 upper-noise source.
Its cap pays the inactive micro interval width/32. The same dimension
works for every capped horizon used in the expected-query proof. -/
noncomputable section
open scoped ENNReal
namespace Bilevel.ChiHierarchyHaar
open ChiHierarchyIndex ChiHierarchyExecution ChiTreeProgress ChiBoundedChain ChiRecursive
  ChiCurvatureSchedule ChiExtensionCalibration

theorem exists_upper_noise_source_dimension (macroN : ℕ) (sc : Scale)
    (cn η Kg p CR ζ Km : ℝ) (weight : ℕ → ℝ)
    (hl : 0<sc.curvature) (hw : 0<sc.width) (hcn : 0≤cn) (hη : 0<η) (hKg : 0<Kg)
    (hweight : ∀ j,0<weight j) (hCR : 0<CR) (hζ : 0<ζ) (hKm : 0<Km) :
    let counts := actualCounts macroN cn η 1 Kg
    let N := sourceHorizon counts 0 p
    let cap := sourcePublicCap macroN 0 sc (sourceRatio 1) (resolution η Kg) weight CR ζ Km
      (sourcePublicWidth sc (sourceRatio 1) (resolution η Kg) 0/2)
    0<cap ∧ ∃ D r : ℕ,∃ b : ℝ,
      sourceDimension macroN cn η 1 Kg≤D ∧
      (∀ j,sourceChainIndex cn (sourceRatio 1 j) (resolution η Kg j)+1≤D) ∧
      (∀ i : FrameIndex counts 0,chainSize i+1≤D) ∧
      (2*(N*batchSize counts 0 (queryVectorCount 1))+1)+
        (N*batchSize counts 0 (queryVectorCount 1))+(r+1)≤D ∧
      0<r ∧ 0<b ∧ b≤2 ∧
      ((N*batchSize counts 0 (queryVectorCount 1):ℕ):ℝ)*
        (((2*(N*batchSize counts 0 (queryVectorCount 1))+1:ℕ):ℝ)*b)≤1/2 ∧
      2*((2*(N*batchSize counts 0 (queryVectorCount 1))+1:ℕ):ℝ)*b≤cap ∧
      ((2*(N*batchSize counts 0 (queryVectorCount 1))+1:ℕ):ℝ≥0∞)*
        GenieProtocol.failurePerQuery (totalColumns counts 0) r b=1/8 := by
  have hres := base_resolution_positive hη hKg
  have hr := sourceRatio_ge_one (by norm_num : (1:ℝ)≤1)
  have hwidth : 0<sourcePublicWidth sc (sourceRatio 1) (resolution η Kg) 0 := by
    change 0<resolution η Kg 0*sc.width/sourceRatio 1 0
    exact div_pos (mul_pos (hres 0) hw) (lt_of_lt_of_le zero_lt_one (hr 0))
  have hcap := (sourcePublicCap_positive macroN 0 sc (sourceRatio 1) (resolution η Kg) weight
    CR ζ Km (sourcePublicWidth sc (sourceRatio 1) (resolution η Kg) 0/2)
    hl hw hr hres hweight hCR hζ hKm (div_pos hwidth (by norm_num))).1
  exact ⟨hcap,exists_uniform_source_dimension macroN 0 (queryVectorCount 1) hcn
    (by norm_num : (1:ℝ)≤1) η Kg p _ hcap⟩

end Bilevel.ChiHierarchyHaar
