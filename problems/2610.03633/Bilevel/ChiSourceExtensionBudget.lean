import Bilevel.ChiScheduledExtensionAssembly
import Bilevel.ChiExtensionUniformCalibration
import Bilevel.ChiOuterExtensionTrace

/-! Actual source hierarchy extension with numerical constants fixed
before every public budget and dimension. This supplies the global
second/third derivative clause of rec:lem:extension-budget. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry ChiExtension ChiCurvatureSchedule

theorem source_extension_budget
    {A Kminus ζ cn η₀ η CR Km Cb t cms δ Cleg : ℝ}
    (hA : 0 ≤ A) (hKminus : 1 ≤ Kminus) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hcn : 0 < cn) (hcn1 : cn ≤ 1) (hη₀ : 0 < η₀) (hη : 0 < η) (hη1 : η ≤ 1)
    (hηsq : η^2 ≤ 1/2) (hlen : 128 ≤ cn/η^2) (hCR : 1 ≤ CR) (hCRcn : ζ*Real.sqrt cn ≤ CR)
    (hKm : 1 ≤ Km) (hCb : 0 < Cb) (ht : 0 < t) (hcms : 0 < cms) (hcms1 : cms ≤ 1/128)
    (hδ : 0 < δ) (hCleg : 1 ≤ Cleg) :
    ∃ Cf CT Cacc c : ℝ,1 ≤ Cf ∧ 1 ≤ CT ∧ 1 ≤ Cacc ∧ 0 < c ∧ c ≤ 1 ∧
    ∀ (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (n : ℕ) (L μ κ θ Δ ε : ℝ) (weight : ℕ → ℝ),
      0 < L → 0 < μ → 1 ≤ κ → 1 ≤ θ → θ ≤ κ → 1/η ≤ κ/6 →
      threshold CT 6 ≤ θ → 1 ≤ ChiIndependentWidths.chosenDepth θ → 0 < ε →
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
      ‖iteratedFDeriv ℝ 2 Ext z‖ ≤ δ ∧
      ‖iteratedFDeriv ℝ 3 Ext z‖ ≤ (θ*μ)/(Cleg*(3*μ/2)) := by
  obtain ⟨C,B,hC,hB,hjets⟩ := scheduled_extension_jets A Kminus ζ cn hA hKminus hζ hζ1 hcn hcn1
  let P := 192*SmallGapLiftSupport.C*η₀*(cn/η^2)
  let Q := 48*SmallGapLiftSupport.C/cms
  let R := 144*CR*η₀
  let S := 64*SmallGapLiftSupport.C*η₀*(cn/η^2)^(1/3:ℝ)
  let V₀ := 72*ζ*η₀
  have hnorm := SmallGapLiftSupport.C_pos
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hV₀ : 0 ≤ V₀ := by dsimp [V₀]; positivity
  obtain ⟨Cf,CT,Cacc,c,Acal,hCf,hCT,hCacc,hc,hc1,hAcal,hAextra,hCfpay,hnum⟩ :=
    exists_uniform_extension_calibration (P:=P) (Q:=Q) (R:=R) (S:=S) (V:=V₀)
      (γ:=1) (Aextra:=1) hC hB hP hQ hR hS hV₀ hCb hη₀ ht hη hη1 hδ (by norm_num) hCleg hcms (by norm_num)
  refine ⟨Cf,CT,Cacc,c,hCf,hCT,hCacc,hc,hc1,?_⟩
  intro E F _ _ _ _ _ _ n L μ κ θ Δ ε weight hL hμ hκ hθ hθκ hK hthreshold hJ hε hwindow hw hw1
  dsimp only
  let J := ChiIndependentWidths.chosenDepth θ
  let T := scale θ CT 6
  let b := sourceWidth Cb ε η₀ L t η J
  let initial : Scale := ⟨η₀*L,b⟩
  have hb : 0 < b := sourceWidth_pos hCb hε hη₀ hL ht hη J
  have hT : 1 ≤ T := (by norm_num : (1:ℝ) ≤ 2).trans (scale_ge_two_above_threshold hCT 6 hthreshold)
  have hTκ : T ≤ κ := (scale_le_parameter (by linarith) hCT 6).trans hθκ
  have ha : 0 < curvature T J := lt_of_lt_of_le zero_lt_one (curvature_bounds hT J).1
  have haT : curvature T J ≤ T := (curvature_bounds hT J).2
  have hbud := hnum L μ κ θ Δ ε (curvature T J) hL hμ hκ hθ hε hwindow hJ ha haT
  intro U V
  let M := sourceMacroNode n initial Km U
  let D := sourceGeometry initial (sourceRatio T) (resolution η (κ/6)) weight A Kminus ζ cn CR V
  have hell : (D J []).ell = η₀*L*curvature T J := by
    obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero (show J ≠ 0 by omega)
    rw [hj]
    exact source_high_node_curvature initial (by linarith) η (κ/6) j
  have hv : 1 ≤ fineParameter (θ*μ) (3*μ/2) ((D J []).ell) (normalCoefficient L J) Cf J := by
    rw [hell]
    exact hbud.1
  refine ⟨hv,?_⟩
  intro hβ blocks normals coarseIndex radialIndex fineIndex z
  have hcfsmall : 2*Cleg*(max 1 (24*SmallGapLiftSupport.C/cms^2)*B^2) ≤ Cf := by
    apply le_trans _ hCfpay
    gcongr
    norm_num
  have hraw := hjets E F n L μ θ η₀ b η κ T CR Km weight hL hμ (by linarith) hθκ hη₀ hb hη hη1 hηsq
    hκ hK hT hTκ hlen hw hw1 hCR hCRcn hKm U V J blocks normals hJ coarseIndex radialIndex fineIndex
    (fun i => hierarchyBlock blocks (i.val+1)) (fun i => hierarchyBlock_norm_le blocks (i.val+1))
    cms Cf (2*Cleg) hcms hcms1 (by linarith) hcfsmall hv hcms hβ z
  have hsecond : 192*SmallGapLiftSupport.C*C^(J+2)*η₀*b*(cn/η^2)*((J:ℝ)+1)^2+
      48*SmallGapLiftSupport.C*B^(J+2)*b/cms+144*CR*η₀*b*((J:ℝ)+1)^2 ≤ δ := by
    convert hbud.2.1 using 1
    dsimp only [P,Q,R]
    ring
  have hthird : 64*SmallGapLiftSupport.C*C^(J+2)*η₀*(cn/η^2)^(1/3:ℝ)*((J:ℝ)+1)^2*T+
      2*θ/(3*(2*Cleg))+72*ζ*η₀*((J:ℝ)+1)^2*T ≤ 2*θ/(3*Cleg) := by
    convert hbud.2.2.1 using 1
    dsimp only [S,V₀]
    ring
  refine ⟨hraw.2.1.trans hsecond,(hraw.2.2.trans hthird).trans_eq ?_⟩
  field_simp
  ring

end Bilevel.ChiExtensionCalibration
