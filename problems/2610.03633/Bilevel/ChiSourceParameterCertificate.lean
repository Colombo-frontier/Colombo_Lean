import Bilevel.ChiSourceUpperCalibration
import Bilevel.ChiSourceExtensionCertificate

/-! One choice of source constants simultaneously normalizes the actual
upper primitive and actual Legendre extension. eta0 is chosen first;
the last accuracy refinement keeps Cf, CT, and the source width formula.
The source extension uses delta=1/12 and CLeg=3. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry ChiExtension ChiCurvatureSchedule

theorem source_parameter_certificate
    {A Kminus ζ cn η CR Km Cb t cms : ℝ}
    (hA : 0 ≤ A) (hKminus : 1 ≤ Kminus) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hcn : 0 < cn) (hcn1 : cn ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1)
    (hlen : 128 ≤ cn/η^2) (hCR : 1 ≤ CR) (hCRcn : ζ*Real.sqrt cn ≤ CR)
    (hKm : 1 ≤ Km) (hCb : 0 < Cb) (ht : 0 < t) (hcms : 0 < cms) (hcms1 : cms ≤ 1/128) :
    ∃ η₀ Cf CT Cacc c : ℝ,0 < η₀ ∧ η₀ ≤ 1 ∧ 1 ≤ Cf ∧ 1 ≤ CT ∧ 1 ≤ Cacc ∧ 0 < c ∧ c ≤ 1 ∧
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
      ∃ hv : 1 ≤ v, (∀ j I,0 < (D j I).width) ∧
      ∀ hβ : 0 < (D J []).width,
      ∀ (blocks normals : ℕ) (coarseIndex radialIndex : Fin J → Fin normals) (fineIndex : Fin normals)
        (z : Full (Joint E (Blocks blocks F)) normals),
      let f₀ := upperBase blocks M (initial.curvature/24) D J
        (weight 0*(ζ*initial.curvature)) (D 0 []).radius
      let Ext := hierarchyExtension blocks M D J cms v hcms hβ hv normals coarseIndex radialIndex fineIndex
        (fun j => weight j*(D j []).nu) (fun j => (D j []).radius) (normalCoefficient L J)
      let H := hidden coarseIndex (coarseFamily blocks M D J) (coarseWidths D J) fineIndex
        (outerFineData blocks M D J cms v hcms hβ hv) (1/normalCoefficient L J)
      ‖iteratedFDeriv ℝ 2 f₀ z.fst‖ ≤ L/4 ∧
      ‖gradient (fun u => f₀ (pack z.fst.fst u)) z.fst.snd‖ ≤ 3*L/4 ∧
      ‖iteratedFDeriv ℝ 2 Ext z‖ ≤ 1/12 ∧
      ‖iteratedFDeriv ℝ 3 Ext z‖ ≤ (θ*μ)/(3*(3*μ/2)) ∧
      ‖iteratedFDeriv ℝ 1 H z‖ ≤ ZeroChainSchedule.width cms (D J []).width v (ZeroChainSchedule.levels v)/16 := by
  obtain ⟨η₀,hη₀,hη₀1,hupper⟩ := source_upper_calibration A Kminus ζ cn CR Km
    hA hKminus hζ hζ1 hcn hcn1 hCR hCRcn hKm
  obtain ⟨Cf,CT,Cold,cold,hCf,hCT,hCold,hcold,hcold1,hext⟩ :=
    source_extension_certificate (δ:=1/12) (Cleg:=3)
      hA hKminus hζ hζ1 hcn hcn1 hη₀ hη hη1 hlen hCR hCRcn hKm hCb ht hcms hcms1 (by norm_num) (by norm_num)
  obtain ⟨Cacc,c,hCacc,hc,hc1,hColdC,hccold,hupper'⟩ :=
    hupper η Cb t Cold cold hη hη1 hlen hCb ht hCold hcold
  refine ⟨η₀,Cf,CT,Cacc,c,hη₀,hη₀1,hCf,hCT,hCacc,hc,hc1,?_⟩
  intro E F _ _ _ _ _ _ n L μ κ θ Δ ε weight hL hμ hθκ hbranch hε hwindow hw hw1
  dsimp only
  let J := ChiIndependentWidths.chosenDepth θ
  let T := scale θ CT 6
  let b := sourceWidth Cb ε η₀ L t η J
  let initial : Scale := ⟨η₀*L,b⟩
  have hbranches := source_branch_conditions hCT hbranch hθκ
  have hθ : 1 ≤ θ := hbranches.1
  have hκ : 1 ≤ κ := hθ.trans hθκ
  have hK : 1/η ≤ κ/6 := hbranches.2.2.1
  have hT : 1 ≤ T := (by norm_num : (1:ℝ) ≤ 2).trans hbranches.2.2.2.2
  have hu := hupper' E F n J L κ θ Δ ε T weight hL hκ hθ hε hK hT hwindow hw hw1
  have he := hext E F n L μ κ θ Δ ε weight hL hμ hθκ hbranch hε hu.1 hw hw1
  have hb : 0 < b := sourceWidth_pos hCb hε hη₀ hL ht hη J
  have hκp : 0 < κ := by linarith
  have hp := parentScale_positive initial (sourceRatio T) (resolution η (κ/6))
    (mul_pos hη₀ hL) hb (sourceRatio_ge_one hT) (base_resolution_positive hη (show 0 < κ/6 by positivity))
  intro U V
  let D := sourceGeometry initial (sourceRatio T) (resolution η (κ/6)) weight A Kminus ζ cn CR V
  obtain ⟨hv,hjets⟩ := he U V
  refine ⟨hv,?_,?_⟩
  · intro j I
    exact (hp (j+1)).2
  · intro hβ blocks normals coarseIndex radialIndex fineIndex z
    have hbase := hu.2 U V J blocks z.fst
    have hjet := hjets hβ blocks normals coarseIndex radialIndex fineIndex z
    exact ⟨hbase.1,hbase.2,hjet.1,hjet.2.1,hjet.2.2⟩

end Bilevel.ChiExtensionCalibration
