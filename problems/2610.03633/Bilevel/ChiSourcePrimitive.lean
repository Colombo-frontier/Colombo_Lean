import Bilevel.ChiHierarchyPrimitive
import Bilevel.ChiSourceParameterCertificate

/-! Actual source primitive existence under one fixed numerical accuracy
window. All analytic jet budgets are discharged by the concrete extension
and upper-base calibration; none is a hypothesis of this theorem. -/
noncomputable section
namespace Bilevel.ChiOuter
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry ChiExtension ChiExtensionCalibration ChiCurvatureSchedule
open scoped RealInnerProductSpace

set_option maxHeartbeats 1200000 in
theorem source_primitive_certificate
    {A Kminus ζ cn η CR Km Cb t cms : ℝ}
    (hA : 0 ≤ A) (hKminus : 1 ≤ Kminus) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hcn : 0 < cn) (hcn1 : cn ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1)
    (hlen : 128 ≤ cn/η^2) (hCR : 1 ≤ CR) (hCRcn : ζ*Real.sqrt cn ≤ CR)
    (hKm : 1 ≤ Km) (hCb : 0 < Cb) (ht : 0 < t) (hcms : 0 < cms) (hcms1 : cms ≤ 1/128) :
    ∃ η₀ Cf CT Cacc c : ℝ,0 < η₀ ∧ η₀ ≤ 1 ∧ 1 ≤ Cf ∧ 1 ≤ CT ∧ 1 ≤ Cacc ∧ 0 < c ∧ c ≤ 1 ∧
    ∀ (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (n : ℕ) (L μ κ θ Δ ε : ℝ) (weight : ℕ → ℝ),
      0 < L → 0 < μ → 2*μ ≤ L → κ=L/μ → θ ≤ κ → sourceBranchThreshold CT η ≤ θ → 0 < ε →
      ε ≤ accuracyWindow c Cacc L κ θ Δ (ChiIndependentWidths.chosenDepth θ) 6 →
      (∀ j,0 < weight j) → (∀ j,weight j ≤ 1) →
      let J := ChiIndependentWidths.chosenDepth θ
      let T := scale θ CT 6
      let initial : Scale := ⟨η₀*L,sourceWidth Cb ε η₀ L t η J⟩
      ∀ (U : Space n →ₗᵢ[ℝ] E)
        (V : ∀ j,List ℕ → Space (sourceChainIndex cn (sourceRatio T j) (resolution η (κ/6) j)) →ₗᵢ[ℝ] F),
      let M := sourceMacroNode n initial Km U
      let D := sourceGeometry initial (sourceRatio T) (resolution η (κ/6)) weight A Kminus ζ cn CR V
      let rad := fun j => weight j*(D j []).nu
      let R := fun j => (D j []).radius
      let v := fineParameter (θ*μ) (3*μ/2) ((D J []).ell) (normalCoefficient L J) Cf J
      ∃ hv : 1 ≤ v, ∃ hwidth : ∀ j I,0 < (D j I).width,
      ∀ (coarseIndex radialIndex : Fin J → Fin (2*J)) (fineIndex : Fin (2*J)),
      let Ext := hierarchyExtension (J+1) M D J cms v hcms (hwidth J []) hv
        (2*J) coarseIndex radialIndex fineIndex rad R (normalCoefficient L J)
      let hExt := hierarchyExtension_contDiff (J+1) M D J cms v hcms (hwidth J []) hv
        (2*J) coarseIndex radialIndex fineIndex rad R (normalCoefficient L J) (fun i => hwidth (i.val+1) [])
      ∃ hb : ∀ z,‖iteratedFDeriv ℝ 2 Ext z‖ ≤ (1:ℝ)/12,
      ∃ P : Model.Primitive (X:=Joint E (Blocks (J+1) F)) (Y:=Joint (Blocks (J+1) F) (Normals (2*J))) μ L L L (θ*μ),
        (∀ x y,P.f x y=hierarchyUpper (J+1) M (initial.curvature/24) D J rad R (2*J) (normalCoefficient L J) x.fst y) ∧
        (∀ x y,P.g x y=extensionLower Ext hExt ⟨1/12,by norm_num⟩ hb
          (by change (1:ℝ)/12<1;norm_num) (3*μ/2) (L/4) x.fst x.snd y) ∧
        ∃ r : P.Response,
          (∀ x,r.y x=pack ((κ/6) • x.snd) (normalTrace Ext x.fst ((κ/6) • x.snd))) ∧
          (∀ x,P.hyperobjective r x=jointOuter (J+1) M (initial.curvature/24) D rad R J (κ/6) x) ∧
          (∀ x y,P.IsLowerSolution x y ↔ y=r.y x) := by
  obtain ⟨η₀,Cf,CT,Cacc,c,hη₀,hη₀1,hCf,hCT,hCacc,hc,hc1,hparameters⟩ :=
    source_parameter_certificate hA hKminus hζ hζ1 hcn hcn1 hη hη1 hlen hCR hCRcn hKm hCb ht hcms hcms1
  refine ⟨η₀,Cf,CT,Cacc,c,hη₀,hη₀1,hCf,hCT,hCacc,hc,hc1,?_⟩
  intro E F _ _ _ _ _ _ n L μ κ θ Δ ε weight hL hμ hμL hκeq hθκ hbranch hε hwindow hw hw1
  have hpars := hparameters E F n L μ κ θ Δ ε weight hL hμ hθκ hbranch hε hwindow hw hw1
  have hbranches := source_branch_conditions hCT hbranch hθκ
  have hJpos := hbranches.2.1
  dsimp only at hpars ⊢
  generalize hJeq : ChiIndependentWidths.chosenDepth θ=J at hpars hJpos ⊢
  cases J with
  | zero => omega
  | succ j =>
    intro U V
    let T := scale θ CT 6
    let initial : Scale := ⟨η₀*L,sourceWidth Cb ε η₀ L t η (j+1)⟩
    let M := sourceMacroNode n initial Km U
    let D := sourceGeometry initial (sourceRatio T) (resolution η (κ/6)) weight A Kminus ζ cn CR V
    let rad := fun k => weight k*(D k []).nu
    let R := fun k => (D k []).radius
    obtain ⟨hv,hwidth,hjets⟩ := hpars U V
    refine ⟨hv,hwidth,?_⟩
    intro coarseIndex radialIndex fineIndex
    have hjet := hjets (hwidth (j+1) []) (j+1+1) (2*(j+1)) coarseIndex radialIndex fineIndex
    have hb := fun z => (hjet z).2.2.1
    have hbase2 (z : Joint E (Blocks (j+1+1) F)) := (hjet (pack z 0)).1
    have hbase1 (x : E) (u : Blocks (j+1+1) F) := (hjet (pack (pack x u) 0)).2.1
    have hT : 1 ≤ T := (by norm_num : (1:ℝ) ≤ 2).trans hbranches.2.2.2.2
    have hκp : 0 < κ := by linarith [hbranches.1]
    have hbp : 0 < initial.width := sourceWidth_pos hCb hε hη₀ hL ht hη (j+1)
    have hp := parentScale_positive initial (sourceRatio T) (resolution η (κ/6))
      (mul_pos hη₀ hL) hbp (sourceRatio_ge_one hT) (base_resolution_positive hη (by positivity : 0 < κ/6))
    have hR (i : Fin (j+1)) : 0 < R (i.val+1) := by
      let s := parentScale initial (sourceRatio T) (resolution η (κ/6)) (i.val+1)
      change 0 < CR*s.force*Real.sqrt (sourceRatio T (i.val+1))/(weight (i.val+1)*(ζ*s.curvature))
      have hforce : 0 < s.force :=
        mul_pos (hp _).1 (hp _).2
      have hr : 0 < sourceRatio T (i.val+1) := lt_of_lt_of_le zero_lt_one (sourceRatio_ge_one hT _)
      exact div_pos (mul_pos (mul_pos (by linarith) hforce) (Real.sqrt_pos.mpr hr))
        (mul_pos (hw _) (mul_pos hζ (hp _).1))
    obtain ⟨P,hf,hg,r,hr,hm,hu⟩ := hierarchy_primitive_of_budgets (j+1+1) M (initial.curvature/24) D j cms _
      hcms (hwidth (j+1) []) hv coarseIndex radialIndex fineIndex rad R (fun i => hwidth (i.val+1) []) hR
      μ L (θ*μ) hμ hμL (mul_nonneg (by linarith [hbranches.1]) hμ.le) hb (fun z => (hjet z).2.2.2.1)
      (fun z => (hbase2 z).trans (by linarith)) hbase1
    have hK : L/(6*μ)=κ/6 := by rw [hκeq];ring
    rw [hK] at hr hm
    exact ⟨hb,P,hf,hg,r,hr,hm,hu⟩

end Bilevel.ChiOuter
