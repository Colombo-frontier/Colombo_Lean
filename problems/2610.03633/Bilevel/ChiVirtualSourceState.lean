import Bilevel.ChiVirtualBorelInverse
import Bilevel.ChiVirtualSourceBudgets

/-! The full-window source calibration applied to the actual disclosed-array
state evaluator. The same constants also retain the actual upper and mean
extension budgets, so the inverse and Primitive use one calibrated family. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.ChiExtensionCalibration
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry ChiExtension ChiCurvatureSchedule ChiIndependentWidths ChiPrefixEvaluation
universe u v
set_option maxHeartbeats 2000000

theorem wide_virtual_state_certificate
    {A Kminus ζ cn η CR Km Cgap Cb t cms Braw : ℝ}
    (hA : 0≤A) (hKminus : 1≤Kminus) (hζ : 0<ζ) (hζ1 : ζ≤1)
    (hcn : 0<cn) (hcn1 : cn≤1) (hη : 0<η) (hη1 : η≤1) (hlen : 128≤cn/η^2)
    (hCR : 1≤CR) (hCRcn : ζ*Real.sqrt cn≤CR) (hKm : 1≤Km) (hCgap : 1≤Cgap)
    (hCb : 0<Cb) (ht : 0<t) (ht1 : t≤1) (hcms : 0<cms) (hcms1 : cms≤1/128) (hBraw : 0≤Braw) :
    ∃ η₀ bStar : ℝ,0<η₀ ∧ η₀≤1 ∧ 0<bStar ∧ bStar≤1 ∧ bStar^2≤1/(256*Cgap) ∧
    ∀ cold : ℝ,0<cold → ∃ Cf CT c : ℝ,1≤Cf ∧ 1≤CT ∧ 0<c ∧ c≤1 ∧ c≤cold ∧
    ∀ (E : Type u) (F : Type v) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (n : ℕ) (L μ κ θ Δ ε : ℝ) (weight : ℕ → ℝ),
      0<L → 0<μ → 2≤κ → θ≤κ^2 → wideBranchThreshold CT≤θ → 0<Δ → 0<ε →
      ε≤c*min L (Real.sqrt (L*Δ)) → (∀ j,0<weight j) → (∀ j,weight j≤1) →
      let J := chosenDepth θ
      let T := scale θ CT 6
      let b := macroWidth bStar Δ (η₀*L)
      let h := middleWidth Cb ε (κ/6) (η₀*L) (t*η) J
      let Kg := b/h
      let initial : Scale := ⟨η₀*L,b⟩
      ∀ (U : Space n →ₗᵢ[ℝ] E)
        (V : ∀ j,List ℕ → Space (sourceChainIndex cn (sourceRatio T j) (resolution η Kg j)) →ₗᵢ[ℝ] F),
      let M := sourceMacroNode n initial Km U
      let D := sourceGeometry initial (sourceRatio T) (resolution η Kg) weight A Kminus ζ cn CR V
      let v := fineParameter (θ*μ) (3*μ/2) ((D J []).ell) (normalCoefficient L J) Cf J
      ∃ hv : 1≤v,
      (∀ j I,0<(D j I).width) ∧ (∀ j I,0<(D j I).radius) ∧
      2*SmallGapLiftSupport.C*Braw*cms*(D J []).ell*((D J []).width)^2/
        (normalCoefficient L J*Real.sqrt v)≤(D J []).width/128 ∧
      (∀ (blocks : ℕ) (x : Joint E (Blocks blocks F)),
        ‖iteratedFDeriv ℝ 2 (upperBase blocks M (initial.curvature/24) D J
          (weight 0*(D 0 []).nu) (D 0 []).radius) x‖≤L/4 ∧
        ‖gradient (fun w => upperBase blocks M (initial.curvature/24) D J
          (weight 0*(D 0 []).nu) (D 0 []).radius (pack x.fst w)) x.snd‖≤L/4) ∧
      ∀ (hβ : 0<(D J []).width) (blocks normals : ℕ)
        (index radialIndex : Fin J → Fin normals) (fineIndex : Fin normals),
      let rad := fun j => weight j*(D j []).nu
      let R := fun j => (D j []).radius
      let Ext := hierarchyExtension blocks M D J cms v hcms hβ hv normals index radialIndex fineIndex rad R (normalCoefficient L J)
      let Ext₀ := hierarchyInactiveExtension blocks M D J cms v hcms hβ hv normals index radialIndex fineIndex rad R (normalCoefficient L J)
      (∀ z,‖iteratedFDeriv ℝ 2 Ext z‖≤1/12 ∧ ‖iteratedFDeriv ℝ 3 Ext z‖≤2*θ/9 ∧
        ‖iteratedFDeriv ℝ 2 Ext₀ z‖≤1/12 ∧ ‖iteratedFDeriv ℝ 3 Ext₀ z‖≤2*θ/9) ∧
      ∀ (rM : ℕ → ℕ) (r : ℕ → ℕ → List ℕ → ℕ) (active : Bool)
        (p : VirtualState M D),ValidState M D rM r p →
      let f := statePotential active blocks M D J rM r cms v normals index radialIndex fineIndex rad R (normalCoefficient L J) p
      ContDiff ℝ 3 f ∧ ∀ z,‖iteratedFDeriv ℝ 2 f z‖≤1/12 ∧ ‖iteratedFDeriv ℝ 3 f z‖≤2*θ/9 := by
  obtain ⟨η₀,bStar,hη₀,hη₀1,hbs,hbs1,hbsgap,hparameter⟩ := wide_virtual_parameter_certificate
    hA hKminus hζ hζ1 hcn hcn1 hη hη1 hlen hCR hCRcn hKm hCgap hCb ht ht1 hcms hcms1 hBraw
  refine ⟨η₀,bStar,hη₀,hη₀1,hbs,hbs1,hbsgap,?_⟩
  intro cold hcold
  obtain ⟨Cf,CT,c,hCf,hCT,hc,hc1,hccold,hpars⟩ := hparameter cold hcold
  refine ⟨Cf,CT,c,hCf,hCT,hc,hc1,hccold,?_⟩
  intro E F _ _ _ _ _ _ n L μ κ θ Δ ε weight hL hμ hκ hθκ hbranch hΔ hε hacc hw hw1
  dsimp only
  let J := chosenDepth θ
  let T := scale θ CT 6
  let b := macroWidth bStar Δ (η₀*L)
  let h := middleWidth Cb ε (κ/6) (η₀*L) (t*η) J
  let Kg := b/h
  let initial : Scale := ⟨η₀*L,b⟩
  intro U V
  let M := sourceMacroNode n initial Km U
  let D := sourceGeometry initial (sourceRatio T) (resolution η Kg) weight A Kminus ζ cn CR V
  let rad := fun j => weight j*(D j []).nu
  let R := fun j => (D j []).radius
  let v := fineParameter (θ*μ) (3*μ/2) (D J []).ell (normalCoefficient L J) Cf J
  obtain ⟨hv,hwidth,hforce,hupper,hjets⟩ := hpars E F n L μ κ θ Δ ε weight
    hL hμ hκ hθκ hbranch hΔ hε hacc hw hw1 U V
  have hT : 1≤T := (by norm_num : (1:ℝ)≤2).trans (wide_branch_conditions hCT hbranch).2.2
  have hbp : 0<b := macroWidth_pos hbs hΔ (mul_pos hη₀ hL)
  have hκp : 0<κ := by linarith only [hκ]
  have hhp : 0<h := by dsimp [h,middleWidth]; positivity
  have hkg : 0<Kg := div_pos hbp hhp
  have hparents := parentScale_positive initial (sourceRatio T) (resolution η Kg)
    (mul_pos hη₀ hL) hbp (sourceRatio_ge_one hT) (base_resolution_positive hη hkg)
  have hradius (j : ℕ) (I : List ℕ) : 0<(D j I).radius :=
    source_radial_radius_pos (by linarith only [hCR]) (hparents j).1 (hparents j).2
      ((by norm_num : (0:ℝ)<1).trans_le (sourceRatio_ge_one hT j)) (hw j) hζ
  refine ⟨hv,hwidth,hradius,hforce,hupper,?_⟩
  intro hβ blocks normals index radialIndex fineIndex
  obtain ⟨hactual,hvirtual⟩ := hjets hβ blocks normals index radialIndex fineIndex
  refine ⟨hactual,?_⟩
  intro rM r active p hp
  have hR : ∀ i : Fin J,0<R (i.val+1) := fun i => hradius (i.val+1) []
  have hC := statePotential_contDiff active blocks M D J rM r cms v hcms hβ hv normals
    index radialIndex fineIndex rad R (normalCoefficient L J) hR (fun i => hwidth (i.val+1) []) p hp
  refine ⟨hC,?_⟩
  intro z
  have hb := hvirtual E F (rM p.1) (r p.1) p.2.1 p.2.2 M.frame
    (fun j I => (D j I).frame) hp.1 hp.2 z
  cases active with
  | false =>
    change ‖iteratedFDeriv ℝ 2 (virtualInactive blocks M D J (rM p.1) (r p.1) p.2.1 p.2.2
      cms v normals index radialIndex fineIndex rad R (normalCoefficient L J)) z‖≤1/12 ∧
      ‖iteratedFDeriv ℝ 3 (virtualInactive blocks M D J (rM p.1) (r p.1) p.2.1 p.2.2
      cms v normals index radialIndex fineIndex rad R (normalCoefficient L J)) z‖≤2*θ/9
    rw [virtualInactive_jet_eq blocks M D J (rM p.1) (r p.1) p.2.1 p.2.2 M.frame
      (fun j I => (D j I).frame) hp.1 hp.2 cms v hcms hβ hv normals index radialIndex fineIndex rad R (normalCoefficient L J) hR 2 z,
      virtualInactive_jet_eq blocks M D J (rM p.1) (r p.1) p.2.1 p.2.2 M.frame
      (fun j I => (D j I).frame) hp.1 hp.2 cms v hcms hβ hv normals index radialIndex fineIndex rad R (normalCoefficient L J) hR 3 z]
    exact ⟨hb.2.2.1,hb.2.2.2⟩
  | true =>
    change ‖iteratedFDeriv ℝ 2 (virtualActive blocks M D J (rM p.1) (r p.1) p.2.1 p.2.2
      cms v normals index radialIndex fineIndex rad R (normalCoefficient L J)) z‖≤1/12 ∧
      ‖iteratedFDeriv ℝ 3 (virtualActive blocks M D J (rM p.1) (r p.1) p.2.1 p.2.2
      cms v normals index radialIndex fineIndex rad R (normalCoefficient L J)) z‖≤2*θ/9
    rw [virtualActive_jet_eq blocks M D J (rM p.1) (r p.1) p.2.1 p.2.2 M.frame
      (fun j I => (D j I).frame) hp.1 hp.2 cms v hcms hβ hv normals index radialIndex fineIndex rad R (normalCoefficient L J) hR 2 z,
      virtualActive_jet_eq blocks M D J (rM p.1) (r p.1) p.2.1 p.2.2 M.frame
      (fun j I => (D j I).frame) hp.1 hp.2 cms v hcms hβ hv normals index radialIndex fineIndex rad R (normalCoefficient L J) hR 3 z]
    exact ⟨hb.1,hb.2.1⟩

end Bilevel.ChiExtensionCalibration
