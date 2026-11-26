import Bilevel.ChiFixedDepthCoarse
import Bilevel.ChiFixedDepthConstants
import Bilevel.ChiUniformFineExtension
import Bilevel.ChiUniformInactiveExtension
import Bilevel.ChiScheduledExtensionAssembly
import Bilevel.ChiScheduledInactiveJets

/-! Actual complete active/inactive extension at fixed depth J=1 and
curvature ratio T=1. No chosen-depth or large-theta premise occurs. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry ChiExtension ChiCurvatureSchedule ChiIndependentWidths

set_option maxHeartbeats 1600000 in
theorem fixed_hierarchy_extension_jets (A Kminus ζ cn : ℝ)
    (hA : 0≤A) (hKm : 1≤Kminus) (hζ : 0<ζ) (hζ1 : ζ≤1) (hcn : 0<cn) (hcn1 : cn≤1) :
    ∃ C Ba Bi : ℝ,1≤C ∧ 1≤Ba ∧ 1≤Bi ∧
    ∀ (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (n : ℕ) (L μ κ η₀ b η t Cb ε Kg CR Km : ℝ) (weight : ℕ → ℝ),
      0<L → 0<μ → 2≤κ → 0<η₀ → 0<b → 0<η → η≤1 →
      0<t → t≤1 → 0≤Cb → 0≤ε → 0<Kg → 1/η≤Kg → 128≤cn/η^2 →
      b/Kg=middleWidth Cb ε (κ/6) (η₀*L) (t*η) 1 →
      (∀ j,0<weight j) → (∀ j,weight j≤1) → 1≤CR → ζ*Real.sqrt cn≤CR → 1≤Km →
      ∀ (U : Space n →ₗᵢ[ℝ] E)
        (V : ∀ j,List ℕ → Space (sourceChainIndex cn (sourceRatio 1 j) (resolution η Kg j)) →ₗᵢ[ℝ] F),
      let initial : Scale := ⟨η₀*L,b⟩
      let M := sourceMacroNode n initial Km U
      let D := sourceGeometry initial (sourceRatio 1) (resolution η Kg) weight A Kminus ζ cn CR V
      ∀ (blocks normals : ℕ) (index radialIndex : Fin 1 → Fin normals) (fineIndex : Fin normals)
        (cms Cf : ℝ),0<cms → cms≤1/128 →
      6*(max 1 (24*SmallGapLiftSupport.C/cms^2)*Ba^2)≤Cf → 4*(Ba^2/t)^2≤Cf →
      6*(max 1 (116*SmallGapLiftSupport.C/cms^2)*Bi^2)≤Cf → 4*(Bi^2/t)^2≤Cf →
      let v := fineParameter μ (3*μ/2) ((D 1 []).ell) (normalCoefficient L 1) Cf 1
      ∀ hv : 1≤v, ∀ hc : 0<cms, ∀ hβ : 0<(D 1 []).width,
      let rad := fun j => weight j*(D j []).nu
      let R := fun j => (D j []).radius
      let Ext := hierarchyExtension blocks M D 1 cms v hc hβ hv normals index radialIndex fineIndex rad R (normalCoefficient L 1)
      let Ext₀ := hierarchyInactiveExtension blocks M D 1 cms v hc hβ hv normals index radialIndex fineIndex rad R (normalCoefficient L 1)
      ∀ z : Full (Joint E (Blocks blocks F)) normals,
      ‖iteratedFDeriv ℝ 2 Ext z‖≤fixedDepthHessian C Cb η₀ η t cn CR cms*(ε/L) ∧
      ‖iteratedFDeriv ℝ 3 Ext z‖≤fixedDepthThird C cn η ζ*η₀+1/9 ∧
      ‖iteratedFDeriv ℝ 2 Ext₀ z‖≤fixedDepthHessian C Cb η₀ η t cn CR cms*(ε/L) ∧
      ‖iteratedFDeriv ℝ 3 Ext₀ z‖≤fixedDepthThird C cn η ζ*η₀+1/9 := by
  obtain ⟨C,hC,hcoarse⟩ := fixed_coarse_extension_jets A Kminus ζ cn hA hKm hζ hζ1 hcn hcn1
  obtain ⟨Ba,hBa,hactive⟩ := wide_fine_extension_jets
  obtain ⟨Bi,hBi,hinactive⟩ := wide_inactive_extension_jets
  refine ⟨C,Ba,Bi,hC,hBa,hBi,?_⟩
  intro E F _ _ _ _ _ _ n L μ κ η₀ b η t Cb ε Kg CR Km weight
    hL hμ hκ hη₀ hb hη hη1 ht ht1 hCb hε hK hthreshold hlen hwidthGain hw hw1 hCR hCRcn hKm' U V
  dsimp only
  let initial : Scale := ⟨η₀*L,b⟩
  let M := sourceMacroNode n initial Km U
  let D := sourceGeometry initial (sourceRatio 1) (resolution η Kg) weight A Kminus ζ cn CR V
  intro blocks normals index radialIndex fineIndex cms Cf hc hcs hCfa hCfaWide hCfi hCfiWide hv hc' hβ z
  let v := fineParameter μ (3*μ/2) ((D 1 []).ell) (normalCoefficient L 1) Cf 1
  let data := outerFineData blocks M D 1 cms v hc' hβ hv
  let rad := fun j => weight j*(D j []).nu
  let R := fun j => (D j []).radius
  let proj := fun i : Fin 1 => hierarchyBlock (E:=E) (F:=F) blocks (i.val+1)
  have hproj (i : Fin 1) : ‖proj i‖≤1 := hierarchyBlock_norm_le blocks (i.val+1)
  have hp := parentScale_positive initial (sourceRatio 1) (resolution η Kg) (mul_pos hη₀ hL) hb
    (sourceRatio_ge_one le_rfl) (base_resolution_positive hη hK)
  have hwidth (i : Fin 1) : 0<(D (i.val+1) []).width := (hp (i.val+2)).2
  have hW (i : Fin 1) : 0<coarseWidths D 1 i := coarseWidth_pos D _ (hwidth i)
  have hco := hcoarse E F n L η₀ b η t Cb ε κ Kg CR Km weight hL hη₀ hb hη hη1 ht hCb hε hκ
    hK hthreshold hlen hwidthGain hw hw1 hCR hCRcn hKm' U V blocks normals index z
  have hκp : 0<κ := by linarith only [hκ]
  have hθκ : (1:ℝ)≤κ^2 := by nlinarith only [hκ]
  have hva : 1≤fineParameter (1*μ) (3*μ/2) ((D 1 []).ell) (normalCoefficient L 1) Cf 1 := by
    simpa only [one_mul] using hv
  have hfa := hactive E F n 1 L μ 1 κ η₀ b η t Cb ε Kg 1 A Kminus ζ cn CR Km weight
    hL hμ (by norm_num) hθκ hκp hη₀ hb hη hη1 ht ht1 hCb hε hK hthreshold (by norm_num) (by norm_num)
    hwidthGain hw hw1 hKm hζ hζ1 hCR hKm' U V blocks normals fineIndex cms Cf 6 hc hcs (by norm_num)
    hCfa hCfaWide hva hc' hβ z
  have hfi := hinactive E F n 1 L μ 1 κ η₀ b η t Cb ε Kg 1 A Kminus ζ cn CR Km weight
    hL hμ (by norm_num) hθκ hκp hη₀ hb hη hη1 ht ht1 hCb hε hK hthreshold (by norm_num) (by norm_num)
    hwidthGain hw hw1 hKm hζ hζ1 hCR hKm' U V blocks normals fineIndex cms Cf 6 hc hcs (by norm_num)
    hCfi hCfiWide hva hc' hβ z
  norm_num only [one_mul,mul_one,show (2:ℝ)/(3*6)=1/9 by norm_num] at hfa hfi
  have hra := fixed_radial_jets radialIndex proj hproj L η₀ b η t Cb ε κ Kg ζ CR
    (fun i => weight (i.val+1)) hL hη₀ hb hη hη1 ht hCb hε hκ hK hζ (by linarith only [hCR])
    (fun i => hw (i.val+1)) (fun i => hw1 (i.val+1)) hwidthGain z
  have hnormal := SmallGapLiftSupport.C_pos
  have hfa2 : ‖iteratedFDeriv ℝ 2 (fun y => fineTerm normals fineIndex data y/normalCoefficient L 1) z‖≤
      (1104*SmallGapLiftSupport.C*Cb/(cms*Real.sqrt (6*η₀)))*(ε/L) := by
    apply hfa.1.trans
    apply mul_le_mul_of_nonneg_right _ (div_nonneg hε hL.le)
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith only [mul_nonneg hnormal.le hCb]
  have hHa2 := source_hidden_add_jet_bound blocks normals M D 1 index fineIndex data (normalCoefficient L 1) hW
    z 2 (by norm_num) _ _ hco.1 hfa2
  have hHa3 := source_hidden_add_jet_bound blocks normals M D 1 index fineIndex data (normalCoefficient L 1) hW
    z 3 (by norm_num) _ _ hco.2 hfa.2
  have hHi2 := hierarchyInactiveHidden_jet_bound blocks M D 1 cms v hc' hβ hv normals index fineIndex
    (normalCoefficient L 1) hwidth z 2 (by norm_num) _ _ hco.1 hfi.1
  have hHi3 := hierarchyInactiveHidden_jet_bound blocks M D 1 cms v hc' hβ hv normals index fineIndex
    (normalCoefficient L 1) hwidth z 3 (by norm_num) _ _ hco.2 hfi.2
  have ha2 := total_jet_bound index (coarseFamily blocks M D 1) (coarseWidths D 1)
    (coarseFamily_contDiff blocks M D 1) hW fineIndex data (1/normalCoefficient L 1)
    radialIndex proj hproj (fun i => rad (i.val+1)) (fun i => R (i.val+1)) (normalCoefficient L 1)
    z 2 (by norm_num) _ _ hHa2 hra.1
  have ha3 := total_jet_bound index (coarseFamily blocks M D 1) (coarseWidths D 1)
    (coarseFamily_contDiff blocks M D 1) hW fineIndex data (1/normalCoefficient L 1)
    radialIndex proj hproj (fun i => rad (i.val+1)) (fun i => R (i.val+1)) (normalCoefficient L 1)
    z 3 (by norm_num) _ _ hHa3 hra.2
  have hi2 := inactive_radial_add_jet_bound blocks M D 1 cms v hc' hβ hv normals index radialIndex fineIndex rad R
    (normalCoefficient L 1) hwidth z 2 (by norm_num) _ _ hHi2 hra.1
  have hi3 := inactive_radial_add_jet_bound blocks M D 1 cms v hc' hβ hv normals index radialIndex fineIndex rad R
    (normalCoefficient L 1) hwidth z 3 (by norm_num) _ _ hHi3 hra.2
  refine ⟨ha2.trans_eq ?_,ha3.trans_eq ?_,hi2.trans_eq ?_,hi3.trans_eq ?_⟩ <;>
    dsimp [fixedDepthHessian,fixedDepthThird] <;> ring

end Bilevel.ChiExtensionCalibration
