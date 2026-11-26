import Bilevel.ChiUniformParameterCertificate
import Bilevel.PolishedIndependentHiddenForce

/-!
The locality calibration in `waI:lem:uniform-locality` requires only
epsilon <= c L. The macro width is free, subject to the stated middle
width separation; no gap parameter or chain-length floor calibration is
used. All Hessian/source/hidden-gradient estimates concern the actual
fixed active and inactive potentials.

This uses the stable inherited normal/flattening objects; the separate
C-infinity source-profile migration requires a fresh dependency rebuild.
-/
noncomputable section
namespace Bilevel.ChiExtensionCalibration
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry ChiExtension
  ChiCurvatureSchedule ChiIndependentWidths

set_option maxHeartbeats 1800000 in
theorem free_middle_locality_budgets
    {A Kminus ζ cn η CR Km η₀ Cb t cms Braw : ℝ}
    (hA : 0 ≤ A) (hKminus : 1 ≤ Kminus) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hcn : 0 < cn) (hcn1 : cn ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1) (hlen : 128 ≤ cn/η^2)
    (hCR : 1 ≤ CR) (hCRcn : ζ*Real.sqrt cn ≤ CR) (hKm : 1 ≤ Km) (hη₀ : 0 < η₀)
    (hCb : 0 < Cb) (ht : 0 < t) (ht1 : t ≤ 1) (hcms : 0 < cms)
    (hcms1 : cms ≤ 1/128) (hBraw : 0 ≤ Braw) (cold : ℝ) (hcold : 0 < cold) :
    ∃ Cg Cf CT c : ℝ,1 ≤ Cg ∧ 1 ≤ Cf ∧ 1 ≤ CT ∧ 0 < c ∧ c ≤ 1 ∧ c ≤ cold ∧
    ∀ (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (n : ℕ) (L μ κ θ ε b : ℝ) (weight : ℕ → ℝ),
      0 < L → 0 < μ → 2 ≤ κ → θ ≤ κ^2 → wideBranchThreshold CT ≤ θ →
      0 < ε → ε ≤ c*L → 0 < b → (∀ j,0 < weight j) → (∀ j,weight j ≤ 1) →
      let J := chosenDepth θ
      let T := scale θ CT 6
      let h := middleWidth Cb ε (κ/6) (η₀*L) (t*η) J
      h/b ≤ η →
      let Kg := b/h
      let initial : Scale := ⟨η₀*L,b⟩
      ∀ (U : Space n →ₗᵢ[ℝ] E)
        (V : ∀ j,List ℕ → Space (sourceChainIndex cn (sourceRatio T j) (resolution η Kg j)) →ₗᵢ[ℝ] F),
      let M := sourceMacroNode n initial Km U
      let D := sourceGeometry initial (sourceRatio T) (resolution η Kg) weight A Kminus ζ cn CR V
      let v := fineParameter (θ*μ) (3*μ/2) ((D J []).ell) (normalCoefficient L J) Cf J
      ∃ hv : 1 ≤ v,
      (∀ j I,0 < (D j I).width) ∧
      2*SmallGapLiftSupport.C*Braw*cms*(D J []).ell*((D J []).width)^2/
        (normalCoefficient L J*Real.sqrt v) ≤ (D J []).width/128 ∧
      ∀ (hβ : 0 < (D J []).width) (blocks normals : ℕ)
        (index radialIndex : Fin J → Fin normals) (fineIndex : Fin normals)
        (z : Full (Joint E (Blocks blocks F)) normals),
      let rad := fun j => weight j*(D j []).nu
      let R := fun j => (D j []).radius
      let Ext := hierarchyExtension blocks M D J cms v hcms hβ hv normals
        index radialIndex fineIndex rad R (normalCoefficient L J)
      let Ext₀ := hierarchyInactiveExtension blocks M D J cms v hcms hβ hv normals
        index radialIndex fineIndex rad R (normalCoefficient L J)
      let H := hidden index (coarseFamily blocks M D J) (coarseWidths D J) fineIndex
        (outerFineData blocks M D J cms v hcms hβ hv) (1/normalCoefficient L J)
      let H₀ := hierarchyInactiveHidden blocks M D J cms v hcms hβ hv normals
        index fineIndex (normalCoefficient L J)
      ‖iteratedFDeriv ℝ 2 Ext z‖ ≤ 1/12 ∧ ‖iteratedFDeriv ℝ 3 Ext z‖ ≤ 2*θ/9 ∧
      ‖iteratedFDeriv ℝ 2 Ext₀ z‖ ≤ 1/12 ∧ ‖iteratedFDeriv ℝ 3 Ext₀ z‖ ≤ 2*θ/9 ∧
      ‖gradient H z‖ ≤ Cg^(J+1)*((η₀*L)/normalCoefficient L J)*h^2 ∧
      ‖gradient H₀ z‖ ≤ Cg^(J+1)*((η₀*L)/normalCoefficient L J)*h^2 := by
  obtain ⟨C,Ba,Bi,hC,hBa,hBi,hjet⟩ := wide_hierarchy_extension_jets A Kminus ζ cn
    hA hKminus hζ hζ1 hcn hcn1
  obtain ⟨Cg,hCg,hhidden⟩ := independent_hidden_gradient_force A Kminus ζ cn
    hA hKminus hζ hζ1 hcn hcn1
  obtain ⟨Cf,CT,c,hCf,hCT,hc,hc1,hccold,hCfa,hCfi,hCfaWide,hCfiWide,hCfForce,hCTc,
    _hCTr,_hCTf,hnum⟩ :=
    exists_wide_extension_constants (C := C) (Bf := Ba) (Bi := Bi) (Braw := Braw)
      (δ := 1/12) (Cleg := 3) hC hBa hBi hBraw hCb hη₀ hη ht hcn hζ
      (lt_of_lt_of_le zero_lt_one hCR) hcms (by norm_num) (by norm_num) hcold
  refine ⟨Cg,Cf,CT,c,hCg,hCf,hCT,hc,hc1,hccold,?_⟩
  intro E F _ _ _ _ _ _ n L μ κ θ ε b weight hL hμ hκ hθκ hbranch hε heL hb hw hw1
  dsimp only
  let J := chosenDepth θ
  let T := scale θ CT 6
  let h := middleWidth Cb ε (κ/6) (η₀*L) (t*η) J
  intro hratio
  let Kg := b/h
  let initial : Scale := ⟨η₀*L,b⟩
  obtain ⟨hθ,hJ,hT2⟩ := wide_branch_conditions hCT hbranch
  have hT : 1 ≤ T := (by norm_num : (1 : ℝ) ≤ 2).trans hT2
  have hκp : 0 < κ := lt_of_lt_of_le zero_lt_two hκ
  have hhp : 0 < h := by dsimp [h,middleWidth]; positivity
  have hKg : 0 < Kg := div_pos hb hhp
  have hKgη : 1/η ≤ Kg := by
    apply (div_le_iff₀ hη).mpr
    have hh := (div_le_iff₀ hb).mp hratio
    dsimp [Kg]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hhp).mpr
    nlinarith only [hh]
  have hgain : b/Kg=middleWidth Cb ε (κ/6) (η₀*L) (t*η) J := by
    change b/(b/h)=h
    field_simp
  have ha : 1 ≤ curvature T J := (curvature_bounds hT J).1
  have haT : curvature T J ≤ T := (curvature_bounds hT J).2
  have hnum' := hnum L μ θ ε (curvature T J) hL hμ hθ hε.le heL hJ ha haT
  intro U V
  let M := sourceMacroNode n initial Km U
  let D := sourceGeometry initial (sourceRatio T) (resolution η Kg) weight A Kminus ζ cn CR V
  have hres := base_resolution_positive hη hKg
  have hp := parentScale_positive initial (sourceRatio T) (resolution η Kg) (mul_pos hη₀ hL) hb
    (sourceRatio_ge_one hT) hres
  have hwidth (j : ℕ) (I : List ℕ) : 0 < (D j I).width := (hp (j+1)).2
  have hell : (D J []).ell=η₀*L*curvature T J := by
    obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero (show J ≠ 0 by omega)
    rw [hj]
    exact source_high_node_curvature initial (lt_of_lt_of_le zero_lt_one hT) η Kg j
  have hwidth0 : (D J []).width=η^J*b/(Kg*curvature T J) :=
    source_parent_width initial hT (mul_pos hη₀ hL) η Kg J
  have hwidthFormula : (D J []).width=
      η^J*middleWidth Cb ε (κ/6) (η₀*L) (t*η) J/curvature T J := by
    rw [hwidth0,← hgain]
    ring
  have hv : 1 ≤ fineParameter (θ*μ) (3*μ/2) ((D J []).ell) (normalCoefficient L J) Cf J := by
    rw [hell]
    exact hnum'.1
  refine ⟨hv,hwidth,?_,?_⟩
  · change 2*SmallGapLiftSupport.C*Braw*cms*(D J []).ell*((D J []).width)^2/
      (normalCoefficient L J*Real.sqrt (fineParameter (θ*μ) (3*μ/2) ((D J []).ell)
        (normalCoefficient L J) Cf J)) ≤ _
    rw [hell,hwidthFormula]
    exact wide_source_force_budget hL hμ hη₀ hCb.le hε.le hκp (zero_le_one.trans hθ) hθκ ha
      ht ht1 hη (lt_of_lt_of_le zero_lt_one hCf) hCfForce hBraw hcms.le J hJ
      hnum'.2.2.1 hnum'.1
  · intro hβ blocks normals index radialIndex fineIndex z
    have hnormal := SmallGapLiftSupport.C_pos
    have hCfa24 : (6 : ℝ)*(max 1 (24*SmallGapLiftSupport.C/cms^2)*Ba^2) ≤ Cf := by
      apply le_trans _ hCfa
      gcongr <;> norm_num
    have hj := hjet E F n L μ θ κ η₀ b η t Cb ε Kg CT CR Km weight hL hμ
      (zero_le_one.trans hθ) hθκ hκp hη₀ hb hη hη1 ht ht1 hCb.le hε.le hKg hKgη
      (lt_of_lt_of_le zero_lt_one hCT) hCTc hT hJ hlen hgain hw hw1 hCR hCRcn hKm
      U V blocks normals index radialIndex fineIndex cms Cf 6 hcms hcms1
      (by norm_num) hCfa24 hCfaWide (by convert hCfi using 1; norm_num) hCfiWide hv hcms hβ z
    have hthird : 64*SmallGapLiftSupport.C*C^(J+2)*η₀*(cn/η^2)^(1/3 : ℝ)*((J : ℝ)+1)^2*T+
        2*θ/(3*6)+72*ζ*η₀*((J : ℝ)+1)^2*T ≤ 2*θ/9 := by
      convert hnum'.2.2.2 using 1 <;> dsimp only [wideThirdCoarse,wideThirdRadial] <;> ring
    have hh := hhidden E F n initial (mul_pos hη₀ hL) hb η Kg T CR Km weight hη hη1 hKg hKgη
      hT hlen hw hw1 hCR hCRcn hKm U V J blocks normals hJ index fineIndex
      (normalCoefficient L J) cms _ (normalCoefficient_pos hL hJ) hcms hcms1 hv hβ z
    have hhab : ‖gradient (hidden index (coarseFamily blocks M D J) (coarseWidths D J)
        fineIndex (outerFineData blocks M D J cms _ hcms hβ hv) (1/normalCoefficient L J)) z‖ ≤
        Cg^(J+1)*((η₀*L)/normalCoefficient L J)*h^2 := by
      simpa only [initial,hgain] using hh.1
    have hhib : ‖gradient (hierarchyInactiveHidden blocks M D J cms _ hcms hβ hv normals
        index fineIndex (normalCoefficient L J)) z‖ ≤
        Cg^(J+1)*((η₀*L)/normalCoefficient L J)*h^2 := by
      simpa only [initial,hgain] using hh.2
    exact ⟨hj.1.trans hnum'.2.1,hj.2.1.trans hthird,hj.2.2.1.trans hnum'.2.1,
      hj.2.2.2.trans hthird,hhab,hhib⟩

end Bilevel.ChiExtensionCalibration
