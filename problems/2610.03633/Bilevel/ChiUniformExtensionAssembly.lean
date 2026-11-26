import Bilevel.ChiUniformCoarseBudgets
import Bilevel.ChiUniformFineExtension
import Bilevel.ChiUniformInactiveExtension
import Bilevel.ChiUniformRadialBudgets
import Bilevel.ChiScheduledExtensionAssembly
import Bilevel.ChiScheduledInactiveJets

/-! Actual complete active and inactive hierarchy jets on the full source
range with independent geometry and response gains. No total-hidden-force
smallness or theta<=kappa restriction enters these regularity bounds. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry ChiExtension ChiCurvatureSchedule ChiIndependentWidths

set_option maxHeartbeats 1600000 in
theorem wide_hierarchy_extension_jets (A Kminus ζ cn : ℝ)
    (hA : 0≤A) (hKm : 1≤Kminus) (hζ : 0<ζ) (hζ1 : ζ≤1) (hcn : 0<cn) (hcn1 : cn≤1) :
    ∃ C Ba Bi : ℝ,1≤C ∧ 1≤Ba ∧ 1≤Bi ∧
    ∀ (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (n : ℕ) (L μ θ κ η₀ b η t Cb ε Kg CT CR Km : ℝ) (weight : ℕ → ℝ),
      0<L → 0<μ → 0≤θ → θ≤κ^2 → 0<κ → 0<η₀ → 0<b → 0<η → η≤1 →
      0<t → t≤1 → 0≤Cb → 0≤ε → 0<Kg → 1/η≤Kg → 0<CT → (C^2/(t*η))^2≤CT →
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
      ∀ (blocks normals : ℕ) (index radialIndex : Fin J → Fin normals) (fineIndex : Fin normals)
        (cms Cf Mpay : ℝ),0<cms → cms≤1/128 → 1≤Mpay →
      Mpay*(max 1 (24*SmallGapLiftSupport.C/cms^2)*Ba^2)≤Cf → 4*(Ba^2/t)^2≤Cf →
      Mpay*(max 1 (116*SmallGapLiftSupport.C/cms^2)*Bi^2)≤Cf → 4*(Bi^2/t)^2≤Cf →
      let v := fineParameter (θ*μ) (3*μ/2) ((D J []).ell) (normalCoefficient L J) Cf J
      ∀ hv : 1≤v, ∀ hc : 0<cms, ∀ hβ : 0<(D J []).width,
      let rad := fun j => weight j*(D j []).nu
      let R := fun j => (D j []).radius
      let Ext := hierarchyExtension blocks M D J cms v hc hβ hv normals index radialIndex fineIndex rad R (normalCoefficient L J)
      let Ext₀ := hierarchyInactiveExtension blocks M D J cms v hc hβ hv normals index radialIndex fineIndex rad R (normalCoefficient L J)
      let H := 192*SmallGapLiftSupport.C*Cb*(cn/η^2)^(2/3:ℝ)+
        1104*SmallGapLiftSupport.C*Cb/(cms*Real.sqrt (6*η₀))+144*CR*Cb
      let Q := 64*SmallGapLiftSupport.C*C^(J+2)*η₀*(cn/η^2)^(1/3:ℝ)*((J:ℝ)+1)^2*scale θ CT 6+
        2*θ/(3*Mpay)+72*ζ*η₀*((J:ℝ)+1)^2*scale θ CT 6
      ∀ z : Full (Joint E (Blocks blocks F)) normals,
      ‖iteratedFDeriv ℝ 2 Ext z‖≤H*(ε/L) ∧ ‖iteratedFDeriv ℝ 3 Ext z‖≤Q ∧
      ‖iteratedFDeriv ℝ 2 Ext₀ z‖≤H*(ε/L) ∧ ‖iteratedFDeriv ℝ 3 Ext₀ z‖≤Q := by
  obtain ⟨C,hC,hcoarse⟩ := wide_coarse_extension_jets A Kminus ζ cn hA hKm hζ hζ1 hcn hcn1
  obtain ⟨Ba,hBa,hactive⟩ := wide_fine_extension_jets
  obtain ⟨Bi,hBi,hinactive⟩ := wide_inactive_extension_jets
  refine ⟨C,Ba,Bi,hC,hBa,hBi,?_⟩
  intro E F _ _ _ _ _ _ n L μ θ κ η₀ b η t Cb ε Kg CT CR Km weight
    hL hμ hθ hθκ hκ hη₀ hb hη hη1 ht ht1 hCb hε hK hthreshold hCT hpay hT hJ hlen
    hwidthGain hw hw1 hCR hCRcn hKm' U V
  dsimp only
  let J := chosenDepth θ
  let T := scale θ CT 6
  let initial : Scale := ⟨η₀*L,b⟩
  let M := sourceMacroNode n initial Km U
  let D := sourceGeometry initial (sourceRatio T) (resolution η Kg) weight A Kminus ζ cn CR V
  intro blocks normals index radialIndex fineIndex cms Cf Mpay hc hcs hMpay hCfa hCfaWide hCfi hCfiWide hv hc' hβ z
  let v := fineParameter (θ*μ) (3*μ/2) ((D J []).ell) (normalCoefficient L J) Cf J
  let data := outerFineData blocks M D J cms v hc' hβ hv
  let rad := fun j => weight j*(D j []).nu
  let R := fun j => (D j []).radius
  let proj := fun i : Fin J => hierarchyBlock (E:=E) (F:=F) blocks (i.val+1)
  have hproj (i : Fin J) : ‖proj i‖≤1 := hierarchyBlock_norm_le blocks (i.val+1)
  have hp := parentScale_positive initial (sourceRatio T) (resolution η Kg) (mul_pos hη₀ hL) hb
    (sourceRatio_ge_one hT) (base_resolution_positive hη hK)
  have hwidth (i : Fin J) : 0<(D (i.val+1) []).width := (hp (i.val+2)).2
  have hW (i : Fin J) : 0<coarseWidths D J i := coarseWidth_pos D _ (hwidth i)
  have hco := hcoarse E F n L η₀ b η t Cb ε κ θ Kg CT CR Km weight hL hη₀ hb hη hη1 ht ht1 hCb hε hκ
    hθ hθκ hK hthreshold hCT hpay hT hJ hlen hwidthGain hw hw1 hCR hCRcn hKm' U V blocks normals index z
  have hfa := hactive E F n J L μ θ κ η₀ b η t Cb ε Kg T A Kminus ζ cn CR Km weight
    hL hμ hθ hθκ hκ hη₀ hb hη hη1 ht ht1 hCb hε hK hthreshold hT hJ hwidthGain
    hw hw1 hKm hζ hζ1 hCR hKm' U V blocks normals fineIndex cms Cf Mpay hc hcs hMpay hCfa hCfaWide hv hc' hβ z
  have hfi := hinactive E F n J L μ θ κ η₀ b η t Cb ε Kg T A Kminus ζ cn CR Km weight
    hL hμ hθ hθκ hκ hη₀ hb hη hη1 ht ht1 hCb hε hK hthreshold hT hJ hwidthGain
    hw hw1 hKm hζ hζ1 hCR hKm' U V blocks normals fineIndex cms Cf Mpay hc hcs hMpay hCfi hCfiWide hv hc' hβ z
  have hpayr : (1/(t*η))^2≤CT := by
    apply le_trans _ hpay
    apply pow_le_pow_left₀ (by positivity)
    exact div_le_div_of_nonneg_right (one_le_pow₀ hC) (mul_nonneg ht.le hη.le)
  have hra := wide_radial_jets L η₀ b η t Cb ε κ θ Kg CT ζ CR hL hη₀ hb hη hη1 ht ht1 hCb hε hκ
    hθ hθκ hK hCT hpayr hT hJ hζ (by linarith) hwidthGain radialIndex proj hproj
    (fun i => weight (i.val+1)) (fun i => hw (i.val+1)) (fun i => hw1 (i.val+1)) z
  have hnormal := SmallGapLiftSupport.C_pos
  have hfa2 : ‖iteratedFDeriv ℝ 2 (fun y => fineTerm normals fineIndex data y/normalCoefficient L J) z‖≤
      (1104*SmallGapLiftSupport.C*Cb/(cms*Real.sqrt (6*η₀)))*(ε/L) := by
    apply hfa.1.trans
    apply mul_le_mul_of_nonneg_right _ (div_nonneg hε hL.le)
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith only [mul_nonneg hnormal.le hCb]
  have hHa2 := source_hidden_add_jet_bound blocks normals M D J index fineIndex data (normalCoefficient L J) hW
    z 2 (by norm_num) _ _ hco.1 hfa2
  have hHa3 := source_hidden_add_jet_bound blocks normals M D J index fineIndex data (normalCoefficient L J) hW
    z 3 (by norm_num) _ _ hco.2 hfa.2
  have hHi2 := hierarchyInactiveHidden_jet_bound blocks M D J cms v hc' hβ hv normals index fineIndex
    (normalCoefficient L J) hwidth z 2 (by norm_num) _ _ hco.1 hfi.1
  have hHi3 := hierarchyInactiveHidden_jet_bound blocks M D J cms v hc' hβ hv normals index fineIndex
    (normalCoefficient L J) hwidth z 3 (by norm_num) _ _ hco.2 hfi.2
  have ha2 := total_jet_bound index (coarseFamily blocks M D J) (coarseWidths D J)
    (coarseFamily_contDiff blocks M D J) hW fineIndex data (1/normalCoefficient L J)
    radialIndex proj hproj (fun i => rad (i.val+1)) (fun i => R (i.val+1)) (normalCoefficient L J)
    z 2 (by norm_num) _ _ hHa2 hra.1
  have ha3 := total_jet_bound index (coarseFamily blocks M D J) (coarseWidths D J)
    (coarseFamily_contDiff blocks M D J) hW fineIndex data (1/normalCoefficient L J)
    radialIndex proj hproj (fun i => rad (i.val+1)) (fun i => R (i.val+1)) (normalCoefficient L J)
    z 3 (by norm_num) _ _ hHa3 hra.2
  have hi2 := inactive_radial_add_jet_bound blocks M D J cms v hc' hβ hv normals index radialIndex fineIndex rad R
    (normalCoefficient L J) hwidth z 2 (by norm_num) _ _ hHi2 hra.1
  have hi3 := inactive_radial_add_jet_bound blocks M D J cms v hc' hβ hv normals index radialIndex fineIndex rad R
    (normalCoefficient L J) hwidth z 3 (by norm_num) _ _ hHi3 hra.2
  refine ⟨ha2.trans_eq ?_,ha3,hi2.trans_eq ?_,hi3⟩ <;> ring

end Bilevel.ChiExtensionCalibration
