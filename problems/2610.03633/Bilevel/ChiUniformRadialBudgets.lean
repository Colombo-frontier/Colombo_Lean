import Bilevel.ChiUniformRadialExtension
import Bilevel.ChiUniformCoarseBudgets

/-! Actual public radial-extension budgets on the full accuracy window. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration
open ChiBoundedChain ChiRecursive ChiCurvatureSchedule ChiExtension PrimitiveGeometry ChiIndependentWidths

theorem wide_radial_jets
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {normals : ℕ} (L η₀ b η t Cb ε κ θ Kg CT ζ CR : ℝ)
    (hL : 0<L) (hη₀ : 0<η₀) (hb : 0<b) (hη : 0<η) (hη1 : η≤1)
    (ht : 0<t) (ht1 : t≤1) (hCb : 0≤Cb) (hε : 0≤ε) (hκ : 0<κ)
    (hθ : 0≤θ) (hθκ : θ≤κ^2) (hK : 0<Kg) (hCT : 0<CT)
    (hpay : (1/(t*η))^2≤CT) (hT : 1≤scale θ CT 6) (hJ : 1≤chosenDepth θ)
    (hζ : 0<ζ) (hCR : 0<CR)
    (hwidthGain : b/Kg=middleWidth Cb ε (κ/6) (η₀*L) (t*η) (chosenDepth θ))
    (index : Fin (chosenDepth θ) → Fin normals)
    (proj : Fin (chosenDepth θ) → E →L[ℝ] F) (hproj : ∀ j,‖proj j‖≤1)
    (weight : Fin (chosenDepth θ) → ℝ) (hw : ∀ j,0<weight j) (hw1 : ∀ j,weight j≤1)
    (z : Full E normals) :
    let J := chosenDepth θ
    let initial : Scale := ⟨η₀*L,b⟩
    let s := fun j : Fin J => parentScale initial (sourceRatio (scale θ CT 6)) (resolution η Kg) (j.val+1)
    let ν := fun j => weight j*(ζ*(s j).curvature)
    let R := fun j => sourceLocalRadius CR (s j).curvature (s j).width
      (sourceRatio (scale θ CT 6) (j.val+1)) (weight j) ζ
    ‖iteratedFDeriv ℝ 2 (radialSum index proj hproj ν R (normalCoefficient L J)) z‖≤
      (144*CR*Cb)*(ε/L) ∧
    ‖iteratedFDeriv ℝ 3 (radialSum index proj hproj ν R (normalCoefficient L J)) z‖≤
      72*ζ*η₀*((J:ℝ)+1)^2*scale θ CT 6 := by
  dsimp only
  let J := chosenDepth θ
  let initial : Scale := ⟨η₀*L,b⟩
  have hj := independent_radial_jets index proj hproj initial η Kg (scale θ CT 6) ζ CR
    (normalCoefficient L J) weight (mul_pos hη₀ hL) hb hη hη1 hK hT hζ hCR
    (normalCoefficient_pos hL hJ) hw hw1 z
  have hω1 : t*η≤1 := by nlinarith only [ht,ht1,hη,hη1]
  have hs := wide_coarse_hessian_factor hL hη₀ hCb hε hκ hθ hθκ
    (by norm_num : (1:ℝ)≤1) (mul_pos ht hη) hω1 hCT (by simpa using hpay)
  simp only [one_pow,one_mul] at hs
  have hr : (scale θ CT 6)^(3/8:ℝ)≤Real.sqrt (scale θ CT 6) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hT (by norm_num)
  have he : initial.force/(Kg*normalCoefficient L J)=
      (η₀*L)*middleWidth Cb ε (κ/6) (η₀*L) (t*η) J/normalCoefficient L J := by
    rw [← hwidthGain]
    dsimp [initial,Scale.force]
    ring
  refine ⟨hj.1.trans ?_,hj.2.trans ?_⟩
  · rw [he]
    have hd := normalCoefficient_pos hL hJ
    have hp : 0≤middleWidth Cb ε (κ/6) (η₀*L) (t*η) J := by unfold middleWidth; positivity
    have hh := mul_le_mul_of_nonneg_left hr
      (show 0≤((η₀*L)*middleWidth Cb ε (κ/6) (η₀*L) (t*η) J/normalCoefficient L J)*(J:ℝ) by positivity)
    have hm := mul_le_mul_of_nonneg_left (hh.trans hs) (show 0≤3*CR by positivity)
    convert hm using 1 <;> ring
  · have hs3 := normal_curvature_depth_factor hL hη₀.le J
    have hTp : 0≤scale θ CT 6 := by linarith
    have hm := mul_le_mul_of_nonneg_left hs3 (show 0≤9*ζ*scale θ CT 6 by positivity)
    convert hm using 1 <;> dsimp only [initial] <;> ring

end Bilevel.ChiExtensionCalibration
