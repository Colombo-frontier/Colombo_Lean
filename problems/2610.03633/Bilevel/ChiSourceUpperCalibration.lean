import Bilevel.ChiOuterSourceUpperBase
import Bilevel.ChiSourceWidthCalibration
import Bilevel.ChiSourcePhysicalScales

/-! Source rec:eq:exact-constants sets L0=eta0*L, with eta0 fixed and
numerically small. The curvature schedule does not multiply L0. This
choice and a refinement of the existing accuracy window pay the actual
upper-base Hessian and lower-gradient budgets. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry

theorem source_upper_calibration (A Kminus ζ cn CR Km : ℝ)
    (hA : 0 ≤ A) (hKminus : 1 ≤ Kminus) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hcn : 0 < cn) (hcn1 : cn ≤ 1) (hCR : 1 ≤ CR) (hCRcn : ζ*Real.sqrt cn ≤ CR) (hKm : 1 ≤ Km) :
    ∃ η₀ : ℝ,0 < η₀ ∧ η₀ ≤ 1 ∧
    ∀ (η Cb t Cold cold : ℝ),0 < η → η ≤ 1 → 128 ≤ cn/η^2 → 0 < Cb → 0 < t → 1 ≤ Cold → 0 < cold →
    ∃ Cacc c : ℝ,1 ≤ Cacc ∧ 0 < c ∧ c ≤ 1 ∧ Cold ≤ Cacc ∧ c ≤ cold ∧
    ∀ (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (n J : ℕ) (L κ θ Δ ε T : ℝ) (weight : ℕ → ℝ),
      0 < L → 1 ≤ κ → 1 ≤ θ → 0 < ε → 1/η ≤ κ/6 → 1 ≤ T →
      ε ≤ accuracyWindow c Cacc L κ θ Δ J 6 →
      (∀ j,0 < weight j) → (∀ j,weight j ≤ 1) →
      ε ≤ accuracyWindow cold Cold L κ θ Δ J 6 ∧
      let b := sourceWidth Cb ε η₀ L t η J
      let initial : Scale := ⟨η₀*L,b⟩
      ∀ (U : Space n →ₗᵢ[ℝ] E)
        (V : ∀ j,List ℕ → Space (sourceChainIndex cn (sourceRatio T j) (resolution η (κ/6) j)) →ₗᵢ[ℝ] F),
      let M := sourceMacroNode n initial Km U
      let D := sourceGeometry initial (sourceRatio T) (resolution η (κ/6)) weight A Kminus ζ cn CR V
      ∀ (depth blocks : ℕ) (z : Joint E (Blocks blocks F)),
      let f₀ := upperBase blocks M (initial.curvature/24) D depth
        (weight 0*(ζ*initial.curvature)) (D 0 []).radius
      ‖iteratedFDeriv ℝ 2 f₀ z‖ ≤ L/4 ∧
      ‖gradient (fun u => f₀ (pack z.fst u)) z.snd‖ ≤ 3*L/4 := by
  obtain ⟨C,hC,hupper⟩ := source_upper_base_budgets A Kminus ζ cn CR Km hA hKminus hζ hζ1 hcn hcn1 hCR hCRcn hKm
  let η₀ := 1/(4*C)
  have hCp : 0 < C := by linarith
  have hη₀ : 0 < η₀ := by dsimp [η₀]; positivity
  have hη₀1 : η₀ ≤ 1 := by dsimp [η₀]; apply (div_le_one (by positivity)).mpr; linarith
  have hCη₀ : C*η₀ = 1/4 := by dsimp [η₀]; field_simp; ring
  refine ⟨η₀,hη₀,hη₀1,?_⟩
  intro η Cb t Cold cold hη hη1 hlen hCb ht hCold hcold
  obtain ⟨Cacc,c,hCacc,hc,hc1,hColdC,hccold,hwidth⟩ := exists_refined_width_budget
    hCb hη₀ ht hη hη1 (show (0:ℝ) < 3 by norm_num) hCold hcold
  refine ⟨Cacc,c,hCacc,hc,hc1,hColdC,hccold,?_⟩
  intro E F _ _ _ _ _ _ n J L κ θ Δ ε T weight hL hκ hθ hε hK hT hwindow hw hw1
  have hwidth' := hwidth L κ θ Δ ε J hL hκ hθ hε hwindow
  refine ⟨hwidth'.1,?_⟩
  dsimp only
  let b := sourceWidth Cb ε η₀ L t η J
  let initial : Scale := ⟨η₀*L,b⟩
  have hb : 0 < b := sourceWidth_pos hCb hε hη₀ hL ht hη J
  have hκp : 0 < κ := by linarith
  have hKp : 0 < κ/6 := by positivity
  have hr := sourceRatio_ge_one hT
  have hres := base_resolution_positive hη hKp
  have hresle := base_resolution_le hKp hK hη
  have hres1 (j : ℕ) : resolution η (κ/6) j ≤ 1 := (hresle j).trans hη1
  have hreslen (j : ℕ) : 128 ≤ cn/(resolution η (κ/6) j)^2 := by
    apply hlen.trans
    apply div_le_div_of_nonneg_left hcn.le (sq_pos_of_pos (hres j))
    nlinarith [hresle j,hres j]
  intro U V depth blocks z
  have hu := hupper E F n initial (mul_pos hη₀ hL) hb (sourceRatio T) (resolution η (κ/6)) weight
    hr rfl hres hres1 hreslen hw hw1 U V depth blocks z
  have he : C*initial.curvature = L/4 := by
    change C*(η₀*L) = L/4
    rw [← mul_assoc,hCη₀]
    ring
  have hf : C*initial.force ≤ 3*L/4 := by
    change C*((η₀*L)*b) ≤ 3*L/4
    rw [show C*((η₀*L)*b) = (C*η₀)*L*b by ring,hCη₀]
    have hh := mul_le_mul_of_nonneg_left hwidth'.2 (show 0 ≤ L/4 by positivity)
    convert hh using 1 <;> ring
  exact ⟨hu.1.trans_eq he,hu.2.trans hf⟩

end Bilevel.ChiExtensionCalibration
