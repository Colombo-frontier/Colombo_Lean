import Bilevel.ChiSourceExtensionBudget
import Bilevel.ChiSourceHiddenSmallness
import Bilevel.ChiSourceBranchThreshold

/-! The actual source extension certificate: global joint regularity and
hidden-force smallness hold for one choice of construction constants and
one accuracy window, uniformly above a fixed branch threshold. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry ChiExtension ChiCurvatureSchedule

theorem source_extension_certificate
    {A Kminus ζ cn η₀ η CR Km Cb t cms δ Cleg : ℝ}
    (hA : 0 ≤ A) (hKminus : 1 ≤ Kminus) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hcn : 0 < cn) (hcn1 : cn ≤ 1) (hη₀ : 0 < η₀) (hη : 0 < η) (hη1 : η ≤ 1)
    (hlen : 128 ≤ cn/η^2) (hCR : 1 ≤ CR) (hCRcn : ζ*Real.sqrt cn ≤ CR)
    (hKm : 1 ≤ Km) (hCb : 0 < Cb) (ht : 0 < t) (hcms : 0 < cms) (hcms1 : cms ≤ 1/128)
    (hδ : 0 < δ) (hCleg : 1 ≤ Cleg) :
    ∃ Cf CT Cacc c : ℝ,1 ≤ Cf ∧ 1 ≤ CT ∧ 1 ≤ Cacc ∧ 0 < c ∧ c ≤ 1 ∧
    ∀ (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (n : ℕ) (L μ κ θ Δ ε : ℝ) (weight : ℕ → ℝ),
      0 < L → 0 < μ → θ ≤ κ → sourceBranchThreshold CT η ≤ θ → 0 < ε →
      ε ≤ accuracyWindow c Cacc L κ θ Δ (ChiIndependentWidths.chosenDepth θ) 6 →
      (∀ j,0 < weight j) → (∀ j,weight j ≤ 1) →
      let J := ChiIndependentWidths.chosenDepth θ
      let T := scale θ CT 6
      let b := sourceWidth Cb ε η₀ L t η J
      let initial : Scale := ⟨η₀*L,b⟩
      ∀ (U : Space n →ₗᵢ[ℝ] E)
        (V : ∀ j,List ℕ → Space (sourceChainIndex cn (sourceRatio T j) (resolution η (κ/6) j)) →ₗᵢ[ℝ] F),
      let M := sourceMacroNode n initial Km U
      let D := sourceGeometry initial (sourceRatio T) (resolution η (κ/6)) weight A Kminus ζ cn CR V
      let v := fineParameter (θ*μ) (3*μ/2) ((D J []).ell) (normalCoefficient L J) Cf J
      ∃ hv : 1 ≤ v, ∀ hβ : 0 < (D J []).width,
      ∀ (blocks normals : ℕ) (coarseIndex radialIndex : Fin J → Fin normals) (fineIndex : Fin normals)
        (z : Full (Joint E (Blocks blocks F)) normals),
      let Ext := hierarchyExtension blocks M D J cms v hcms hβ hv normals coarseIndex radialIndex fineIndex
        (fun j => weight j*(D j []).nu) (fun j => (D j []).radius) (normalCoefficient L J)
      let H := hidden coarseIndex (coarseFamily blocks M D J) (coarseWidths D J) fineIndex
        (outerFineData blocks M D J cms v hcms hβ hv) (1/normalCoefficient L J)
      ‖iteratedFDeriv ℝ 2 Ext z‖ ≤ δ ∧
      ‖iteratedFDeriv ℝ 3 Ext z‖ ≤ (θ*μ)/(Cleg*(3*μ/2)) ∧
      ‖iteratedFDeriv ℝ 1 H z‖ ≤ ZeroChainSchedule.width cms (D J []).width v (ZeroChainSchedule.levels v)/16 := by
  have hηsq : η^2 ≤ 1/2 := by
    have hh := (le_div_iff₀ (sq_pos_of_pos hη)).mp hlen
    nlinarith only [hh,hcn1]
  obtain ⟨Cf,CT,Cold,cold,hCf,hCT,hCold,hcold,hcold1,hbudget⟩ :=
    source_extension_budget hA hKminus hζ hζ1 hcn hcn1 hη₀ hη hη1 hηsq hlen hCR hCRcn hKm hCb ht hcms hcms1 hδ hCleg
  obtain ⟨Cacc,c,hCacc,hc,hc1,hColdC,hccold,hhidden⟩ :=
    source_hidden_smallness hA hKminus hζ hζ1 hcn hcn1 hη₀ hη hη1 hηsq hlen hCR hCRcn hKm hCb ht hcms hcms1 hCold hcold
  refine ⟨Cf,CT,Cacc,c,hCf,hCT,hCacc,hc,hc1,?_⟩
  intro E F _ _ _ _ _ _ n L μ κ θ Δ ε weight hL hμ hθκ hbranch hε hwindow hw hw1
  dsimp only
  let J := ChiIndependentWidths.chosenDepth θ
  let T := scale θ CT 6
  have hbranches := source_branch_conditions hCT hbranch hθκ
  have hθ : 1 ≤ θ := hbranches.1
  have hκ : 1 ≤ κ := hθ.trans hθκ
  have hJ : 1 ≤ J := hbranches.2.1
  have hK : 1/η ≤ κ/6 := hbranches.2.2.1
  have hT : 1 ≤ T := (by norm_num : (1:ℝ) ≤ 2).trans hbranches.2.2.2.2
  have hTκ : T ≤ κ := (scale_le_parameter (by linarith) hCT 6).trans hθκ
  have hh := hhidden E F n J L μ κ θ Δ ε T Cf weight hL hμ hκ hθ hK hT hTκ hCf hJ hε hwindow hw hw1
  have hb := hbudget E F n L μ κ θ Δ ε weight hL hμ hκ hθ hθκ hK hbranches.2.2.2.1 hJ hε hh.1 hw hw1
  intro U V
  obtain ⟨hv,hderiv⟩ := hb U V
  refine ⟨hv,?_⟩
  intro hβ blocks normals coarseIndex radialIndex fineIndex z
  exact ⟨(hderiv hβ blocks normals coarseIndex radialIndex fineIndex z).1,
    (hderiv hβ blocks normals coarseIndex radialIndex fineIndex z).2,
    hh.2 U V hv hβ blocks normals coarseIndex fineIndex z⟩

end Bilevel.ChiExtensionCalibration
