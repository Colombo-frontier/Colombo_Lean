import Bilevel.ChiFixedDepthPhysical
import Bilevel.ChiUniformCoarseExtension
import Bilevel.ChiUniformRadialExtension

/-! Actual coarse and public radial extension jets at J=1,T=1. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry ChiExtension ChiCurvatureSchedule ChiIndependentWidths

theorem fixed_coarse_extension_jets (A Kminus ζ cn : ℝ)
    (hA : 0≤A) (hKm : 1≤Kminus) (hζ : 0<ζ) (hζ1 : ζ≤1) (hcn : 0<cn) (hcn1 : cn≤1) :
    ∃ C : ℝ,1≤C ∧
    ∀ (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (n : ℕ) (L η₀ b η t Cb ε κ Kg CR Km : ℝ) (weight : ℕ → ℝ),
      0<L → 0<η₀ → 0<b → 0<η → η≤1 → 0<t → 0≤Cb → 0≤ε → 2≤κ →
      0<Kg → 1/η≤Kg → 128≤cn/η^2 →
      b/Kg=middleWidth Cb ε (κ/6) (η₀*L) (t*η) 1 →
      (∀ j,0<weight j) → (∀ j,weight j≤1) → 1≤CR → ζ*Real.sqrt cn≤CR → 1≤Km →
      ∀ (U : Space n →ₗᵢ[ℝ] E)
        (V : ∀ j,List ℕ → Space (sourceChainIndex cn (sourceRatio 1 j) (resolution η Kg j)) →ₗᵢ[ℝ] F),
      let initial : Scale := ⟨η₀*L,b⟩
      let M := sourceMacroNode n initial Km U
      let D := sourceGeometry initial (sourceRatio 1) (resolution η Kg) weight A Kminus ζ cn CR V
      ∀ (blocks normals : ℕ) (index : Fin 1 → Fin normals) (z : Full (Joint E (Blocks blocks F)) normals),
      ‖iteratedFDeriv ℝ 2 (sourceCoarseExtension blocks normals M D 1 index (normalCoefficient L 1)) z‖≤
        (96*SmallGapLiftSupport.C*C^3*Cb/(t*η)*(cn/η^2)^(2/3:ℝ))*(ε/L) ∧
      ‖iteratedFDeriv ℝ 3 (sourceCoarseExtension blocks normals M D 1 index (normalCoefficient L 1)) z‖≤
        64*SmallGapLiftSupport.C*C^3*η₀*(cn/η^2)^(1/3:ℝ) := by
  obtain ⟨C,hC,hcoarse⟩ := independent_coarse_extension_jets A Kminus ζ cn hA hKm hζ hζ1 hcn hcn1
  refine ⟨C,hC,?_⟩
  intro E F _ _ _ _ _ _ n L η₀ b η t Cb ε κ Kg CR Km weight
    hL hη₀ hb hη hη1 ht hCb hε hκ hK hthreshold hlen hwidth hw hw1 hCR hCRcn hKm' U V
  dsimp only
  intro blocks normals index z
  have hh := hcoarse E F n ⟨η₀*L,b⟩ (mul_pos hη₀ hL) hb η Kg 1 CR Km weight hη hη1 hK hthreshold
    (by norm_num) hlen hw hw1 hCR hCRcn hKm' U V 1 blocks normals index (normalCoefficient L 1)
    (normalCoefficient_pos hL (by norm_num)) z
  simp only [Nat.cast_one,Real.sqrt_one,mul_one] at hh
  have hnormal := SmallGapLiftSupport.C_pos
  have hC0 : 0≤C := by linarith only [hC]
  constructor
  · apply hh.1.trans
    have hf := mul_le_mul_of_nonneg_left (fixed_depth_force_factor hL hη₀ hCb hε hκ ht hη hwidth)
      (show 0≤4*SmallGapLiftSupport.C*C^3*(cn/η^2)^(2/3:ℝ) by positivity)
    convert hf using 1 <;> ring
  · apply hh.2.trans
    have hf := mul_le_mul_of_nonneg_left (fixed_depth_normal_curvature hη₀.le hL)
      (show 0≤8*SmallGapLiftSupport.C*C^3*(cn/η^2)^(1/3:ℝ) by positivity)
    convert hf using 1 <;> ring

theorem fixed_radial_jets
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {m : ℕ} (index : Fin 1 → Fin m) (proj : Fin 1 → E →L[ℝ] F) (hproj : ∀ j,‖proj j‖≤1)
    (L η₀ b η t Cb ε κ Kg ζ CR : ℝ) (weight : Fin 1 → ℝ)
    (hL : 0<L) (hη₀ : 0<η₀) (hb : 0<b) (hη : 0<η) (hη1 : η≤1) (ht : 0<t)
    (hCb : 0≤Cb) (hε : 0≤ε) (hκ : 2≤κ) (hK : 0<Kg) (hζ : 0<ζ) (hCR : 0<CR)
    (hw : ∀ j,0<weight j) (hw1 : ∀ j,weight j≤1)
    (hwidth : b/Kg=middleWidth Cb ε (κ/6) (η₀*L) (t*η) 1) (z : Full E m) :
    let initial : Scale := ⟨η₀*L,b⟩
    let s := fun j : Fin 1 => parentScale initial (sourceRatio 1) (resolution η Kg) (j.val+1)
    let ν := fun j => weight j*(ζ*(s j).curvature)
    let R := fun j => sourceLocalRadius CR (s j).curvature (s j).width (sourceRatio 1 (j.val+1)) (weight j) ζ
    ‖iteratedFDeriv ℝ 2 (radialSum index proj hproj ν R (normalCoefficient L 1)) z‖≤
      (72*CR*Cb/(t*η))*(ε/L) ∧
    ‖iteratedFDeriv ℝ 3 (radialSum index proj hproj ν R (normalCoefficient L 1)) z‖≤72*ζ*η₀ := by
  dsimp only
  have hh := independent_radial_jets index proj hproj ⟨η₀*L,b⟩ η Kg 1 ζ CR (normalCoefficient L 1) weight
    (mul_pos hη₀ hL) hb hη hη1 hK (by norm_num) hζ hCR
    (normalCoefficient_pos hL (by norm_num)) hw hw1 z
  simp only [Nat.cast_one,Real.one_rpow,mul_one] at hh
  constructor
  · apply hh.1.trans
    have hf := mul_le_mul_of_nonneg_left (fixed_depth_force_factor hL hη₀ hCb hε hκ ht hη hwidth)
      (show 0≤3*CR by positivity)
    convert hf using 1
    dsimp [Scale.force]
    ring
  · apply hh.2.trans
    have hf := mul_le_mul_of_nonneg_left (fixed_depth_normal_curvature hη₀.le hL)
      (show 0≤9*ζ by positivity)
    convert hf using 1
    ring

end Bilevel.ChiExtensionCalibration
