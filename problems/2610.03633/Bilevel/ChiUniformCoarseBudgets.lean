import Bilevel.ChiUniformCoarseExtension
import Bilevel.ChiUniformPhysicalBudgets

/-! The sharp actual coarse ledger at the wide source parameters. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry ChiExtension ChiCurvatureSchedule ChiIndependentWidths

theorem normal_curvature_depth_factor {L η₀ : ℝ} (hL : 0<L) (hη₀ : 0≤η₀) (J : ℕ) :
    (η₀*L/normalCoefficient L J)*(J:ℝ)≤8*η₀*((J:ℝ)+1)^2 := by
  have hh := mul_le_mul_of_nonneg_left (sqrt_depth_product J) (show 0≤4*η₀ by positivity)
  have he : (η₀*L/normalCoefficient L J)*(J:ℝ)=4*η₀*(Real.sqrt (2*(J:ℝ))*(J:ℝ)) := by
    unfold normalCoefficient
    field_simp
    ring
  rw [he]
  exact hh.trans_eq (by ring)

theorem wide_coarse_extension_jets (A Kminus ζ cn : ℝ)
    (hA : 0≤A) (hKm : 1≤Kminus) (hζ : 0<ζ) (hζ1 : ζ≤1) (hcn : 0<cn) (hcn1 : cn≤1) :
    ∃ C : ℝ,1≤C ∧
    ∀ (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (n : ℕ) (L η₀ b η t Cb ε κ θ Kg CT CR Km : ℝ) (weight : ℕ → ℝ),
      0<L → 0<η₀ → 0<b → 0<η → η≤1 → 0<t → t≤1 → 0≤Cb → 0≤ε → 0<κ →
      0≤θ → θ≤κ^2 → 0<Kg → 1/η≤Kg → 0<CT → (C^2/(t*η))^2≤CT →
      1≤scale θ CT 6 → 1≤chosenDepth θ → 128≤cn/η^2 →
      b/Kg=middleWidth Cb ε (κ/6) (η₀*L) (t*η) (chosenDepth θ) →
      (∀ j,0<weight j) → (∀ j,weight j≤1) → 1≤CR → ζ*Real.sqrt cn≤CR → 1≤Km →
      ∀ (U : Space n →ₗᵢ[ℝ] E)
        (V : ∀ j,List ℕ → Space (sourceChainIndex cn (sourceRatio (scale θ CT 6) j)
          (resolution η Kg j)) →ₗᵢ[ℝ] F),
      let J := chosenDepth θ
      let initial : Scale := ⟨η₀*L,b⟩
      let M := sourceMacroNode n initial Km U
      let D := sourceGeometry initial (sourceRatio (scale θ CT 6)) (resolution η Kg) weight A Kminus ζ cn CR V
      ∀ (blocks normals : ℕ) (index : Fin J → Fin normals) (z : Full (Joint E (Blocks blocks F)) normals),
      ‖iteratedFDeriv ℝ 2 (sourceCoarseExtension blocks normals M D J index (normalCoefficient L J)) z‖≤
        (192*SmallGapLiftSupport.C*Cb*(cn/η^2)^(2/3:ℝ))*(ε/L) ∧
      ‖iteratedFDeriv ℝ 3 (sourceCoarseExtension blocks normals M D J index (normalCoefficient L J)) z‖≤
        64*SmallGapLiftSupport.C*C^(J+2)*η₀*(cn/η^2)^(1/3:ℝ)*((J:ℝ)+1)^2*scale θ CT 6 := by
  obtain ⟨C,hC,hjet⟩ := independent_coarse_extension_jets A Kminus ζ cn hA hKm hζ hζ1 hcn hcn1
  refine ⟨C,hC,?_⟩
  intro E F _ _ _ _ _ _ n L η₀ b η t Cb ε κ θ Kg CT CR Km weight
    hL hη₀ hb hη hη1 ht ht1 hCb hε hκ hθ hθκ hK hthreshold hCT hpay hT hJ hlen
    hwidthGain hw hw1 hCR hCRcn hKm' U V
  dsimp only
  let J := chosenDepth θ
  let initial : Scale := ⟨η₀*L,b⟩
  intro blocks normals index z
  have hj := hjet E F n initial (mul_pos hη₀ hL) hb η Kg (scale θ CT 6) CR Km weight
    hη hη1 hK hthreshold hT hlen hw hw1 hCR hCRcn hKm' U V J blocks normals index
    (normalCoefficient L J) (normalCoefficient_pos hL hJ) z
  have hω1 : t*η≤1 := by nlinarith only [ht,ht1,hη,hη1]
  have hs := wide_coarse_hessian_factor hL hη₀ hCb hε hκ hθ hθκ hC (mul_pos ht hη) hω1 hCT hpay
  have hCnormal := SmallGapLiftSupport.C_pos
  refine ⟨hj.1.trans ?_,hj.2.trans ?_⟩
  · change 4*SmallGapLiftSupport.C*C^(J+2)*((η₀*L)*b/(Kg*normalCoefficient L J))*(J:ℝ)*
      (cn/η^2)^(2/3:ℝ)*Real.sqrt (scale θ CT 6)≤_
    have he : (η₀*L)*b/(Kg*normalCoefficient L J)=
        (η₀*L)*middleWidth Cb ε (κ/6) (η₀*L) (t*η) J/normalCoefficient L J := by
      rw [← hwidthGain]
      ring
    rw [he]
    have hm := mul_le_mul_of_nonneg_left hs
      (show 0≤4*SmallGapLiftSupport.C*(cn/η^2)^(2/3:ℝ) by positivity)
    convert hm using 1 <;> ring
  · have hs3 := normal_curvature_depth_factor hL hη₀.le J
    have hm := mul_le_mul_of_nonneg_left hs3
      (show 0≤8*SmallGapLiftSupport.C*C^(J+2)*(cn/η^2)^(1/3:ℝ)*scale θ CT 6 by
        have hp : 0≤scale θ CT 6 := by linarith
        positivity)
    convert hm using 1 <;> dsimp only [initial] <;> ring

end Bilevel.ChiExtensionCalibration
