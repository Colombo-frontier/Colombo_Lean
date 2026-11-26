import Bilevel.ChiScheduledHiddenForce
import Bilevel.ChiFineBlindScale
import Bilevel.ChiHiddenBudgetArithmetic
import Bilevel.ChiAccuracyWindowRefinement

/-! The actual total hidden gradient is small relative to the actual
finest fine normal width. Tightening the accuracy window preserves all
previously calibrated regularity budgets and leaves Cf and CT unchanged. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry ChiExtension ChiCurvatureSchedule

theorem source_hidden_smallness
    {A Kminus ζ cn η₀ η CR Km Cb t cms Cold cold : ℝ}
    (hA : 0 ≤ A) (hKminus : 1 ≤ Kminus) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hcn : 0 < cn) (hcn1 : cn ≤ 1) (hη₀ : 0 < η₀) (hη : 0 < η) (hη1 : η ≤ 1)
    (hηsq : η^2 ≤ 1/2) (hlen : 128 ≤ cn/η^2) (hCR : 1 ≤ CR) (hCRcn : ζ*Real.sqrt cn ≤ CR)
    (hKm : 1 ≤ Km) (hCb : 0 < Cb) (ht : 0 < t) (hcms : 0 < cms) (hcms1 : cms ≤ 1/128)
    (hCold : 1 ≤ Cold) (hcold : 0 < cold) :
    ∃ Cacc c : ℝ,1 ≤ Cacc ∧ 0 < c ∧ c ≤ 1 ∧ Cold ≤ Cacc ∧ c ≤ cold ∧
    ∀ (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (n J : ℕ) (L μ κ θ Δ ε T Cf : ℝ) (weight : ℕ → ℝ),
      0 < L → 0 < μ → 1 ≤ κ → 1 ≤ θ → 1/η ≤ κ/6 → 1 ≤ T → T ≤ κ → 1 ≤ Cf → 1 ≤ J → 0 < ε →
      ε ≤ accuracyWindow c Cacc L κ θ Δ J 6 →
      (∀ j,0 < weight j) → (∀ j,weight j ≤ 1) →
      ε ≤ accuracyWindow cold Cold L κ θ Δ J 6 ∧
      let b := sourceWidth Cb ε η₀ L t η J
      let initial : Scale := ⟨η₀*L,b⟩
      ∀ (U : Space n →ₗᵢ[ℝ] E)
        (V : ∀ j,List ℕ → Space (sourceChainIndex cn (sourceRatio T j) (resolution η (κ/6) j)) →ₗᵢ[ℝ] F),
      let M := sourceMacroNode n initial Km U
      let D := sourceGeometry initial (sourceRatio T) (resolution η (κ/6)) weight A Kminus ζ cn CR V
      let v := fineParameter (θ*μ) (3*μ/2) ((D J []).ell) (normalCoefficient L J) Cf J
      ∀ hv : 1 ≤ v, ∀ hβ : 0 < (D J []).width,
      ∀ (blocks normals : ℕ) (index : Fin J → Fin normals) (fineIndex : Fin normals)
        (z : Full (Joint E (Blocks blocks F)) normals),
      ‖iteratedFDeriv ℝ 1 (hidden index (coarseFamily blocks M D J) (coarseWidths D J) fineIndex
        (outerFineData blocks M D J cms v hcms hβ hv) (1/normalCoefficient L J)) z‖ ≤
        ZeroChainSchedule.width cms (D J []).width v (ZeroChainSchedule.levels v)/16 := by
  obtain ⟨Cforce,hCforce,hforce⟩ := scheduled_hidden_force A Kminus ζ cn hA hKminus hζ hζ1 hcn hcn1
  obtain ⟨Cacc,c,hCacc,hc,hc1,hColdC,hccold,hcal⟩ := exists_refined_hidden_ratio
    (show 0 ≤ Cforce by linarith) hCb.le hη₀ ht hη hη1 (show 0 < cms/100 by positivity) hCold hcold
  refine ⟨Cacc,c,hCacc,hc,hc1,hColdC,hccold,?_⟩
  intro E F _ _ _ _ _ _ n J L μ κ θ Δ ε T Cf weight hL hμ hκ hθ hK hT hTκ hCf hJ hε hwindow hw hw1
  have hcal' := hcal L κ θ Δ ε J hL hκ hθ hwindow
  refine ⟨hcal'.1,?_⟩
  dsimp only
  let b := sourceWidth Cb ε η₀ L t η J
  let initial : Scale := ⟨η₀*L,b⟩
  have hb : 0 < b := sourceWidth_pos hCb hε hη₀ hL ht hη J
  have hκp : 0 < κ := by linarith
  have hθp : 0 < θ := by linarith
  have hKp : 0 < κ/6 := by positivity
  have hsmall := hidden_gradient_from_accuracy_ratio (show 0 ≤ Cforce by linarith) hη₀.le hη hb.le
    hKp hθp J hcal'.2
  intro U V
  let M := sourceMacroNode n initial Km U
  let D := sourceGeometry initial (sourceRatio T) (resolution η (κ/6)) weight A Kminus ζ cn CR V
  intro hv hβ blocks normals index fineIndex z
  let v := fineParameter (θ*μ) (3*μ/2) ((D J []).ell) (normalCoefficient L J) Cf J
  have hell : (D J []).ell = η₀*L*curvature T J := by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show J ≠ 0 by omega)
    exact source_high_node_curvature initial (by linarith) η (κ/6) j
  have hwidth : (D J []).width = η^J*b/((κ/6)*curvature T J) := by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show J ≠ 0 by omega)
    exact source_parent_width initial hT (mul_pos hη₀ hL) η (κ/6) (j+1)
  have hv' : 1 ≤ fineParameter (θ*μ) (3*μ/2) (η₀*L*curvature T J) (normalCoefficient L J) Cf J := by
    have hh : 1 ≤ v := hv
    dsimp only [v] at hh
    rwa [hell] at hh
  have hW : 6*cms*η₀*η^J*b/((κ/6)*θ) ≤
      ZeroChainSchedule.width cms (D J []).width v (ZeroChainSchedule.levels v) := by
    dsimp only [v]
    rw [hell,hwidth]
    exact source_fine_blind_width hθp hμ hL hη₀ hη hb hKp (curvature_pos (by linarith) J)
      hCf hcms hcms1 J hJ hv'
  have hraw := hforce E F n L η₀ b η κ T CR Km weight hL hη₀ hb hη hη1 hηsq hκ hK hT hTκ hlen
    hw hw1 hCR hCRcn hKm U V J blocks normals hJ index fineIndex cms v hcms hcms1 hv hβ z
  apply (hraw.trans hsmall).trans
  apply le_trans _ (div_le_div_of_nonneg_right hW (by norm_num : (0:ℝ) ≤ 16))
  have hbase : 0 ≤ cms*η₀*η^J*b/((κ/6)*θ) := by positivity
  have hh := mul_le_mul_of_nonneg_right (show (1:ℝ)/50 ≤ 3/8 by norm_num) hbase
  convert hh using 1 <;> ring

end Bilevel.ChiExtensionCalibration
