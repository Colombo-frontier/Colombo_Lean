import Bilevel.ChiVirtualSourceState
import Bilevel.ChiHierarchyPrimitive
import Bilevel.ChiHierarchyOrigin

/-! One calibrated actual Primitive and all valid-state virtual potentials.
The same source constants control the actual and virtual inverse Hessians. -/
noncomputable section
namespace Bilevel.ChiOuter
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry ChiExtension ChiExtensionCalibration ChiCurvatureSchedule ChiIndependentWidths ChiPrefixEvaluation

set_option maxHeartbeats 1200000 in
theorem wide_virtual_primitive_certificate
    {A Kminus ζ cn η CR Km Cgap Cb t cms Braw : ℝ}
    (hA : 0≤A) (hKminus : 1≤Kminus) (hζ : 0<ζ) (hζ1 : ζ≤1)
    (hcn : 0<cn) (hcn1 : cn≤1) (hη : 0<η) (hη1 : η≤1) (hlen : 128≤cn/η^2)
    (hCR : 1≤CR) (hCRcn : ζ*Real.sqrt cn≤CR) (hKm : 1≤Km) (hCgap : 1≤Cgap)
    (hCb : 0<Cb) (ht : 0<t) (ht1 : t≤1) (hcms : 0<cms) (hcms1 : cms≤1/128) (hBraw : 0≤Braw) :
    ∃ η₀ bStar : ℝ,0<η₀ ∧ η₀≤1 ∧ 0<bStar ∧ bStar≤1 ∧ bStar^2≤1/(256*Cgap) ∧
    ∀ cold : ℝ,0<cold → ∃ Cf CT c : ℝ,1≤Cf ∧ 1≤CT ∧ 0<c ∧ c≤1 ∧ c≤cold ∧
    ∀ (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (n : ℕ) (L μ κ θ Δ ε : ℝ) (weight : ℕ → ℝ),
      0<L → 0<μ → 2≤κ → κ=L/μ → θ≤κ^2 → wideBranchThreshold CT≤θ → 0<Δ → 0<ε →
      ε≤c*min L (Real.sqrt (L*Δ)) → (∀ j,0<weight j) → (∀ j,weight j≤1) →
      let J := chosenDepth θ
      let T := scale θ CT 6
      let b := macroWidth bStar Δ (η₀*L)
      let h := middleWidth Cb ε (κ/6) (η₀*L) (t*η) J
      let Kg := b/h
      let initial : Scale := ⟨η₀*L,b⟩
      ∀ (U : Space n →ₗᵢ[ℝ] E)
        (V : ∀ j,List ℕ → Space (sourceChainIndex cn (sourceRatio T j) (resolution η Kg j)) →ₗᵢ[ℝ] F),
      let M : Node E := sourceMacroNode n initial Km U
      let D : Geometry F := sourceGeometry initial (sourceRatio T) (resolution η Kg) weight A Kminus ζ cn CR V
      let rad := fun j => weight j*(D j []).nu
      let R := fun j => (D j []).radius
      let v : ℝ := fineParameter (θ*μ) (3*μ/2) ((D J []).ell) (normalCoefficient L J) Cf J
      ∃ hv : 1≤v, ∃ hwidth : ∀ j I,0<(D j I).width,
      2*SmallGapLiftSupport.C*Braw*cms*(D J []).ell*((D J []).width)^2/
        (normalCoefficient L J*Real.sqrt v)≤(D J []).width/128 ∧
      ∀ (coarseIndex radialIndex : Fin J → Fin (2*J)) (fineIndex : Fin (2*J)),
      let Ext := hierarchyExtension (J+1) M D J cms v hcms (hwidth J []) hv (2*J)
        coarseIndex radialIndex fineIndex rad R (normalCoefficient L J)
      let Ext₀ := hierarchyInactiveExtension (J+1) M D J cms v hcms (hwidth J []) hv (2*J)
        coarseIndex radialIndex fineIndex rad R (normalCoefficient L J)
      let hExt : ContDiff ℝ 3 Ext := hierarchyExtension_contDiff (J+1) M D J cms v hcms (hwidth J []) hv (2*J)
        coarseIndex radialIndex fineIndex rad R (normalCoefficient L J) (fun i => hwidth (i.val+1) [])
      ∃ hb : ∀ z,‖iteratedFDeriv ℝ 2 Ext z‖≤(1:ℝ)/12,
      (∀ z,‖iteratedFDeriv ℝ 2 Ext₀ z‖≤(1:ℝ)/12) ∧
      (∀ (rM : ℕ → ℕ) (r : ℕ → ℕ → List ℕ → ℕ) (active : Bool)
        (p : VirtualState M D),ValidState M D rM r p →
        let f := statePotential active (J+1) M D J rM r cms v (2*J)
          coarseIndex radialIndex fineIndex rad R (normalCoefficient L J) p
        ContDiff ℝ 3 f ∧ ∀ z,‖iteratedFDeriv ℝ 2 f z‖≤1/12 ∧ ‖iteratedFDeriv ℝ 3 f z‖≤2*θ/9) ∧
      ∃ P : Model.Primitive (X:=Joint E (Blocks (J+1) F)) (Y:=Joint (Blocks (J+1) F) (Normals (2*J))) μ L L L (θ*μ),
      (∀ x y,P.f x y=hierarchyUpper (J+1) M (initial.curvature/24) D J rad R (2*J) (normalCoefficient L J) x.fst y) ∧
      (∀ x y,P.g x y=extensionLower Ext hExt ⟨1/12,by norm_num⟩ hb
        (by change (1:ℝ)/12<1;norm_num) (3*μ/2) (L/4) x.fst x.snd y) ∧
      ∃ r : P.Response,r.y 0=0 ∧
        (∀ x,r.y x=pack ((κ/6) • x.snd) (normalTrace Ext x.fst ((κ/6) • x.snd))) ∧
        (∀ x,P.hyperobjective r x=jointOuter (J+1) M (initial.curvature/24) D rad R J (κ/6) x) ∧
        (∀ x y,P.IsLowerSolution x y ↔ y=r.y x) := by
  obtain ⟨η₀,bStar,hη₀,hη₀1,hbs,hbs1,hbsgap,hparameter⟩ := wide_virtual_state_certificate
    hA hKminus hζ hζ1 hcn hcn1 hη hη1 hlen hCR hCRcn hKm hCgap hCb ht ht1 hcms hcms1 hBraw
  refine ⟨η₀,bStar,hη₀,hη₀1,hbs,hbs1,hbsgap,?_⟩
  intro cold hcold
  obtain ⟨Cf,CT,c,hCf,hCT,hc,hc1,hccold,hpars⟩ := hparameter cold hcold
  refine ⟨Cf,CT,c,hCf,hCT,hc,hc1,hccold,?_⟩
  intro E F _ _ _ _ _ _ n L μ κ θ Δ ε weight hL hμ hκ hκeq hθκ hbranch hΔ hε hacc hw hw1
  have hp0 := hpars E F n L μ κ θ Δ ε weight hL hμ hκ hθκ hbranch hΔ hε hacc hw hw1
  have hbranches := wide_branch_conditions hCT hbranch
  have hJpos := hbranches.2.1
  have hμL : 2*μ≤L := (le_div_iff₀ hμ).mp (by rwa [← hκeq])
  dsimp only at hp0 ⊢
  generalize hJeq : chosenDepth θ=J at hp0 hJpos ⊢
  cases J with
  | zero => omega
  | succ j =>
    intro U V
    let T := scale θ CT 6
    let b := macroWidth bStar Δ (η₀*L)
    let h := middleWidth Cb ε (κ/6) (η₀*L) (t*η) (j+1)
    let Kg := b/h
    let initial : Scale := ⟨η₀*L,b⟩
    let M : Node E := sourceMacroNode n initial Km U
    let D : Geometry F := sourceGeometry initial (sourceRatio T) (resolution η Kg) weight A Kminus ζ cn CR V
    let rad := fun k => weight k*(D k []).nu
    let R := fun k => (D k []).radius
    obtain ⟨hv,hwidth,hradius,hforce,hupper,hjets⟩ := hp0 U V
    refine ⟨hv,hwidth,hforce,?_⟩
    intro coarseIndex radialIndex fineIndex
    obtain ⟨hjet,hvirtual⟩ := hjets (hwidth (j+1) []) (j+1+1) (2*(j+1)) coarseIndex radialIndex fineIndex
    have hb := fun z => (hjet z).1
    have hR (i : Fin (j+1)) : 0<R (i.val+1) := hradius (i.val+1) []
    have hethird : 2*θ/9=(θ*μ)/(3*(3*μ/2)) := by field_simp; ring
    obtain ⟨P,hf,hg,r,hr,hm,hu⟩ := hierarchy_primitive_of_budgets (j+1+1) M (initial.curvature/24) D j cms _
      hcms (hwidth (j+1) []) hv coarseIndex radialIndex fineIndex rad R (fun i => hwidth (i.val+1) []) hR
      μ L (θ*μ) hμ hμL (mul_nonneg (by linarith [hbranches.1]) hμ.le) hb
      (fun z => (hjet z).2.1.trans_eq hethird)
      (fun z => (hupper (j+1+1) z).1.trans (by linarith))
      (fun x u => (hupper (j+1+1) (pack x u)).2.trans (by linarith))
    have hK : L/(6*μ)=κ/6 := by rw [hκeq]; ring
    rw [hK] at hr hm
    have hrzero := hierarchy_response_origin (j+1+1) M D (j+1) cms _ hcms (hwidth (j+1) []) hv
      (2*(j+1)) coarseIndex radialIndex fineIndex rad R (normalCoefficient L (j+1))
      (fun i => hwidth (i.val+1) []) hR r.y (κ/6) hr
    exact ⟨hb,(fun z => (hjet z).2.2.1),hvirtual,P,hf,hg,r,hrzero,hr,hm,hu⟩

end Bilevel.ChiOuter
