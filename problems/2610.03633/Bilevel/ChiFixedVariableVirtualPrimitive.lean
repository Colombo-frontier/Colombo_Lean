import Bilevel.ChiFixedVariableVirtualParameters
import Bilevel.ChiHierarchyPrimitive
import Bilevel.ChiHierarchyOrigin

/-! The actual fixed-depth primitive, with variation budget `theta*mu`.
The extension is constructed from the source geometry; its derivatives
are conclusions of the fixed-depth calibration. -/
noncomputable section
namespace Bilevel.ChiOuter
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry ChiExtension ChiExtensionCalibration ChiCurvatureSchedule ChiIndependentWidths ChiPrefixEvaluation

set_option maxHeartbeats 1200000 in
theorem fixed_variable_virtual_primitive_certificate {A Kminus ζ cn η CR Km Cb t cms : ℝ}
    (hA : 0≤A) (hKm : 1≤Kminus) (hζ : 0<ζ) (hζ1 : ζ≤1) (hcn : 0<cn) (hcn1 : cn≤1)
    (hη : 0<η) (hη1 : η≤1) (hlen : 128≤cn/η^2) (hCR : 1≤CR) (hCRcn : ζ*Real.sqrt cn≤CR)
    (hKm' : 1≤Km) (hCb : 0<Cb) (ht : 0<t) (ht1 : t≤1) (hcms : 0<cms) (hcms1 : cms≤1/128) :
    ∃ η₀ Cf c : ℝ,0<η₀ ∧ η₀≤1 ∧ 1≤Cf ∧ 0<c ∧ c≤1 ∧
    ∀ (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (n : ℕ) (L μ θ κ b ε Kg : ℝ) (weight : ℕ → ℝ),
      0<L → 0<μ → 1≤θ → θ≤κ^2 → 2≤κ → κ=L/μ → 0<b → b≤1 → 0≤ε → ε≤c*L → 0<Kg → 1/η≤Kg →
      b/Kg=middleWidth Cb ε (κ/6) (η₀*L) (t*η) 1 →
      (∀ j,0<weight j) → (∀ j,weight j≤1) →
      ∀ (U : Space n →ₗᵢ[ℝ] E)
        (V : ∀ j,List ℕ → Space (sourceChainIndex cn (sourceRatio 1 j) (resolution η Kg j)) →ₗᵢ[ℝ] F),
      let initial : Scale := ⟨η₀*L,b⟩
      let M := sourceMacroNode n initial Km U
      let D := sourceGeometry initial (sourceRatio 1) (resolution η Kg) weight A Kminus ζ cn CR V
      let rad := fun j => weight j*(D j []).nu
      let R := fun j => (D j []).radius
      let v := fineParameter (θ*μ) (3*μ/2) ((D 1 []).ell) (normalCoefficient L 1) Cf 1
      ∃ hv : 1≤v, ∃ hwidth : ∀ j I,0<(D j I).width,
      ∀ (coarseIndex radialIndex : Fin 1 → Fin 2) (fineIndex : Fin 2),
      let Ext := hierarchyExtension 2 M D 1 cms v hcms (hwidth 1 []) hv 2
        coarseIndex radialIndex fineIndex rad R (normalCoefficient L 1)
      let Ext₀ := hierarchyInactiveExtension 2 M D 1 cms v hcms (hwidth 1 []) hv 2
        coarseIndex radialIndex fineIndex rad R (normalCoefficient L 1)
      let hExt : ContDiff ℝ 3 Ext := hierarchyExtension_contDiff 2 M D 1 cms v hcms (hwidth 1 []) hv 2
        coarseIndex radialIndex fineIndex rad R (normalCoefficient L 1) (fun i => hwidth (i.val+1) [])
      ∃ hb : ∀ z,‖iteratedFDeriv ℝ 2 Ext z‖≤(1:ℝ)/12,
      (∀ z,‖iteratedFDeriv ℝ 2 Ext₀ z‖≤(1:ℝ)/12) ∧
      (∀ (rM : ℕ → ℕ) (r : ℕ → ℕ → List ℕ → ℕ) (active : Bool)
        (p : VirtualState M D),ValidState M D rM r p →
        let f := statePotential active 2 M D 1 rM r cms v 2 coarseIndex radialIndex fineIndex rad R (normalCoefficient L 1) p
        ContDiff ℝ 3 f ∧ ∀ z,‖iteratedFDeriv ℝ 2 f z‖≤(1:ℝ)/12 ∧ ‖iteratedFDeriv ℝ 3 f z‖≤(2*θ:ℝ)/9) ∧
      ∃ P : Model.Primitive (X:=Joint E (Blocks 2 F)) (Y:=Joint (Blocks 2 F) (Normals 2)) μ L L L (θ*μ),
      (∀ x y,P.f x y=hierarchyUpper 2 M (initial.curvature/24) D 1 rad R 2 (normalCoefficient L 1) x.fst y) ∧
      (∀ x y,P.g x y=extensionLower Ext hExt ⟨1/12,by norm_num⟩ hb
        (by change (1:ℝ)/12<1;norm_num) (3*μ/2) (L/4) x.fst x.snd y) ∧
      ∃ r : P.Response,r.y 0=0 ∧
        (∀ x,r.y x=pack ((κ/6) • x.snd) (normalTrace Ext x.fst ((κ/6) • x.snd))) ∧
        (∀ x,P.hyperobjective r x=jointOuter 2 M (initial.curvature/24) D rad R 1 (κ/6) x) ∧
        (∀ x y,P.IsLowerSolution x y ↔ y=r.y x) := by
  obtain ⟨η₀,Cf,c,hη₀,hη₀1,hCf,hc,hc1,hparameter⟩ := fixed_variable_virtual_parameter_certificate
    hA hKm hζ hζ1 hcn hcn1 hη hη1 hlen hCR hCRcn hKm' hCb ht ht1 hcms hcms1
  refine ⟨η₀,Cf,c,hη₀,hη₀1,hCf,hc,hc1,?_⟩
  intro E F _ _ _ _ _ _ n L μ θ κ b ε Kg weight hL hμ hθ hθκ hκ hκeq hb0 hb1 hε hacc hKg hKgη hgain hw hw1 U V
  dsimp only
  let initial : Scale := ⟨η₀*L,b⟩
  let M := sourceMacroNode n initial Km U
  let D := sourceGeometry initial (sourceRatio 1) (resolution η Kg) weight A Kminus ζ cn CR V
  let rad := fun j => weight j*(D j []).nu
  let R := fun j => (D j []).radius
  obtain ⟨hv,hwidth,hupper,hjets⟩ := hparameter E F n L μ θ κ b ε Kg weight
    hL hμ hθ hθκ hκ hb0 hb1 hε hacc hKg hKgη hgain hw hw1 U V
  refine ⟨hv,hwidth,?_⟩
  intro coarseIndex radialIndex fineIndex
  have hj := (hjets 2 2 coarseIndex radialIndex fineIndex (hwidth 1 [])).1
  have hvirtual := (hjets 2 2 coarseIndex radialIndex fineIndex (hwidth 1 [])).2
  have hb := fun z => (hj z).1
  have hp := parentScale_positive initial (sourceRatio 1) (resolution η Kg)
    (mul_pos hη₀ hL) hb0 (sourceRatio_ge_one le_rfl) (base_resolution_positive hη hKg)
  have hR (i : Fin 1) : 0<R (i.val+1) := by
    let s := parentScale initial (sourceRatio 1) (resolution η Kg) (i.val+1)
    change 0<CR*s.force*Real.sqrt (sourceRatio 1 (i.val+1))/(weight (i.val+1)*(ζ*s.curvature))
    have hf : 0<s.force := mul_pos (hp _).1 (hp _).2
    have hr : 0<sourceRatio 1 (i.val+1) := lt_of_lt_of_le zero_lt_one (sourceRatio_ge_one le_rfl _)
    exact div_pos (mul_pos (mul_pos (by linarith only [hCR]) hf) (Real.sqrt_pos.mpr hr))
      (mul_pos (hw _) (mul_pos hζ (hp _).1))
  have hμL : 2*μ≤L := (le_div_iff₀ hμ).mp (by rwa [← hκeq])
  have hethird : (2*θ:ℝ)/9=(θ*μ)/(3*(3*μ/2)) := by field_simp; ring
  obtain ⟨P,hf,hg,r,hr,hm,hu⟩ := hierarchy_primitive_of_budgets 2 M (initial.curvature/24) D 0 cms _
    hcms (hwidth 1 []) hv coarseIndex radialIndex fineIndex rad R (fun i => hwidth (i.val+1) []) hR
    μ L (θ*μ) hμ hμL (mul_nonneg (by linarith only [hθ]) hμ.le) hb (fun z => (hj z).2.1.trans_eq hethird)
    (fun z => (hupper 2 z).1.trans (by linarith only [hL]))
    (fun x u => (hupper 2 (pack x u)).2.trans (by linarith only [hL]))
  have hK : L/(6*μ)=κ/6 := by rw [hκeq]; ring
  rw [hK] at hr hm
  have hrzero := hierarchy_response_origin 2 M D 1 cms _ hcms (hwidth 1 []) hv
    2 coarseIndex radialIndex fineIndex rad R (normalCoefficient L 1)
    (fun i => hwidth (i.val+1) []) hR r.y (κ/6) hr
  exact ⟨hb,(fun z => (hj z).2.2.1),hvirtual,P,hf,hg,r,hrzero,hr,hm,hu⟩

end Bilevel.ChiOuter

