import Bilevel.ChiUniformExtensionAssembly
import Bilevel.ChiUniformExtensionConstants
import Bilevel.ChiUniformUpperBase

/-! Complete actual independent-width parameter certificate on the full
source accuracy window. Curvature and macro width are fixed first; the
extension constants are then chosen while preserving any earlier window. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry ChiExtension ChiCurvatureSchedule ChiIndependentWidths

def wideBranchThreshold (CT : ℝ) : ℝ := max (threshold CT 6) (Real.exp 4)

theorem wide_branch_conditions {CT θ : ℝ} (hCT : 1≤CT) (hθ : wideBranchThreshold CT≤θ) :
    1≤θ ∧ 1≤chosenDepth θ ∧ 2≤scale θ CT 6 := by
  have hth : threshold CT 6≤θ := (le_max_left _ _).trans hθ
  have hθ1 : 1≤θ := (le_max_left _ _).trans hth
  have he : Real.exp 4≤θ := (le_max_right _ _).trans hθ
  refine ⟨hθ1,?_,scale_ge_two_above_threshold hCT 6 hth⟩
  have hu := chosenDepth_upper hθ1
  have hl := Real.log_le_log (Real.exp_pos 4) (show Real.exp 4≤2+θ by linarith)
  rw [Real.log_exp] at hl
  by_contra hn
  have hz : chosenDepth θ=0 := by omega
  rw [hz] at hu
  norm_num at hu
  linarith

set_option maxHeartbeats 1800000 in
theorem wide_parameter_certificate
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
      (∀ j I,0<(D j I).width) ∧
      2*SmallGapLiftSupport.C*Braw*cms*(D J []).ell*((D J []).width)^2/
        (normalCoefficient L J*Real.sqrt v)≤(D J []).width/128 ∧
      (∀ (blocks : ℕ) (x : Joint E (Blocks blocks F)),
        ‖iteratedFDeriv ℝ 2 (upperBase blocks M (initial.curvature/24) D J
          (weight 0*(D 0 []).nu) (D 0 []).radius) x‖≤L/4 ∧
        ‖gradient (fun w => upperBase blocks M (initial.curvature/24) D J
          (weight 0*(D 0 []).nu) (D 0 []).radius (pack x.fst w)) x.snd‖≤L/4) ∧
      ∀ (hβ : 0<(D J []).width) (blocks normals : ℕ)
        (index radialIndex : Fin J → Fin normals) (fineIndex : Fin normals)
        (z : Full (Joint E (Blocks blocks F)) normals),
      let rad := fun j => weight j*(D j []).nu
      let R := fun j => (D j []).radius
      let Ext := hierarchyExtension blocks M D J cms v hcms hβ hv normals index radialIndex fineIndex rad R (normalCoefficient L J)
      let Ext₀ := hierarchyInactiveExtension blocks M D J cms v hcms hβ hv normals index radialIndex fineIndex rad R (normalCoefficient L J)
      ‖iteratedFDeriv ℝ 2 Ext z‖≤1/12 ∧ ‖iteratedFDeriv ℝ 3 Ext z‖≤2*θ/9 ∧
      ‖iteratedFDeriv ℝ 2 Ext₀ z‖≤1/12 ∧ ‖iteratedFDeriv ℝ 3 Ext₀ z‖≤2*θ/9 := by
  obtain ⟨C,Ba,Bi,hC,hBa,hBi,hjet⟩ := wide_hierarchy_extension_jets A Kminus ζ cn hA hKminus hζ hζ1 hcn hcn1
  obtain ⟨η₀,bStar,hη₀,hη₀1,hbs,hbs1,hbsgap,hupper⟩ := uniform_upper_base_certificate A Kminus ζ cn CR Km Cgap
    hA hKminus hζ hζ1 hcn hcn1 hCR hCRcn hKm hCgap
  refine ⟨η₀,bStar,hη₀,hη₀1,hbs,hbs1,hbsgap,?_⟩
  intro cold hcold
  obtain ⟨cw,hcw,hcw1,hwidthcal⟩ := exists_uniform_width_calibration
    (cS:=128*bStar^2) hη₀ hη₀1 hbs hcn (by norm_num : (0:ℝ)<1/6) hCb (mul_pos ht hη) hη
    (by norm_num : (0:ℝ)<1) (by ring_nf; rfl)
  obtain ⟨Cf,CT,c,hCf,hCT,hc,hc1,hccold,hCfa,hCfi,hCfaWide,hCfiWide,hCfForce,hCTc,_hCTr,_hCTf,hnum⟩ :=
    exists_wide_extension_constants (C:=C) (Bf:=Ba) (Bi:=Bi) (Braw:=Braw) (δ:=1/12) (Cleg:=3)
      hC hBa hBi hBraw hCb hη₀ hη ht hcn hζ (lt_of_lt_of_le zero_lt_one hCR) hcms (by norm_num) (by norm_num)
      (show 0<min cold cw from lt_min hcold hcw)
  have hcold' : c≤cold := hccold.trans (min_le_left _ _)
  have hcw' : c≤cw := hccold.trans (min_le_right _ _)
  refine ⟨Cf,CT,c,hCf,hCT,hc,hc1,hcold',?_⟩
  intro E F _ _ _ _ _ _ n L μ κ θ Δ ε weight hL hμ hκ hθκ hbranch hΔ hε hacc hw hw1
  dsimp only
  let J := chosenDepth θ
  let T := scale θ CT 6
  let b := macroWidth bStar Δ (η₀*L)
  let h := middleWidth Cb ε (κ/6) (η₀*L) (t*η) J
  let Kg := b/h
  let initial : Scale := ⟨η₀*L,b⟩
  obtain ⟨hθ,hJ,hT2⟩ := wide_branch_conditions hCT hbranch
  have hT : 1≤T := (by norm_num : (1:ℝ)≤2).trans hT2
  have hκp : 0<κ := lt_of_lt_of_le zero_lt_two hκ
  have hbp : 0<b := macroWidth_pos hbs hΔ (mul_pos hη₀ hL)
  have hhp : 0<h := by dsimp [h,middleWidth]; positivity
  have hKg : 0<Kg := div_pos hbp hhp
  have hwidecw : ε≤cw*min L (Real.sqrt (L*Δ)) :=
    hacc.trans (mul_le_mul_of_nonneg_right hcw' (by positivity))
  have hwidthcert := hwidthcal L Δ κ θ (κ/6) ε hL hΔ hκ hθ hθκ (by ring_nf; rfl) hε hwidecw
  have hratio : h/b≤η := hwidthcert.2.1
  have hKgη : 1/η≤Kg := by
    apply (div_le_iff₀ hη).mpr
    have hh := (div_le_iff₀ hbp).mp hratio
    dsimp [Kg]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hhp).mpr
    nlinarith only [hh]
  have hgain : b/Kg=middleWidth Cb ε (κ/6) (η₀*L) (t*η) J := by
    change b/(b/h)=h
    field_simp
  have heL : ε≤c*L := hacc.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hc.le)
  have ha : 1≤curvature T J := (curvature_bounds hT J).1
  have haT : curvature T J≤T := (curvature_bounds hT J).2
  have hnum' := hnum L μ θ ε (curvature T J) hL hμ hθ hε.le heL hJ ha haT
  intro U V
  let M := sourceMacroNode n initial Km U
  let D := sourceGeometry initial (sourceRatio T) (resolution η Kg) weight A Kminus ζ cn CR V
  have hres := base_resolution_positive hη hKg
  have hresle := base_resolution_le hKg hKgη hη
  have hres1 (j : ℕ) : resolution η Kg j≤1 := (hresle j).trans hη1
  have hreslen (j : ℕ) : 128≤cn/(resolution η Kg j)^2 := by
    apply hlen.trans
    apply div_le_div_of_nonneg_left hcn.le (sq_pos_of_pos (hres j))
    exact pow_le_pow_left₀ (hres j).le (hresle j) 2
  have hp := parentScale_positive initial (sourceRatio T) (resolution η Kg) (mul_pos hη₀ hL) hbp
    (sourceRatio_ge_one hT) hres
  have hwidth (j : ℕ) (I : List ℕ) : 0<(D j I).width := (hp (j+1)).2
  have hell : (D J []).ell=η₀*L*curvature T J := by
    obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero (show J≠0 by omega)
    rw [hj]
    exact source_high_node_curvature initial (lt_of_lt_of_le zero_lt_one hT) η Kg j
  have hwidth0 : (D J []).width=η^J*b/(Kg*curvature T J) := by
    obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero (show J≠0 by omega)
    rw [hj]
    exact source_parent_width initial hT (mul_pos hη₀ hL) η Kg (j+1)
  have hwidthFormula : (D J []).width=η^J*middleWidth Cb ε (κ/6) (η₀*L) (t*η) J/curvature T J := by
    rw [hwidth0,← hgain]
    ring
  have hv : 1≤fineParameter (θ*μ) (3*μ/2) ((D J []).ell) (normalCoefficient L J) Cf J := by
    rw [hell]
    exact hnum'.1
  refine ⟨hv,hwidth,?_,?_,?_⟩
  · change 2*SmallGapLiftSupport.C*Braw*cms*(D J []).ell*((D J []).width)^2/
      (normalCoefficient L J*Real.sqrt (fineParameter (θ*μ) (3*μ/2) ((D J []).ell) (normalCoefficient L J) Cf J))≤_
    rw [hell,hwidthFormula]
    exact wide_source_force_budget hL hμ hη₀ hCb.le hε.le hκp (zero_le_one.trans hθ) hθκ ha ht ht1 hη
      (lt_of_lt_of_le zero_lt_one hCf) hCfForce hBraw hcms.le J hJ hnum'.2.2.1 hnum'.1
  · intro blocks x
    exact hupper E F n L Δ hL hΔ (sourceRatio T) (resolution η Kg) weight (sourceRatio_ge_one hT) rfl
      hres hres1 hreslen hw hw1 U V J blocks x
  · intro hβ blocks normals index radialIndex fineIndex z
    have hnormal := SmallGapLiftSupport.C_pos
    have hCfa24 : (6:ℝ)*(max 1 (24*SmallGapLiftSupport.C/cms^2)*Ba^2)≤Cf := by
      apply le_trans _ hCfa
      gcongr <;> norm_num
    have hj := hjet E F n L μ θ κ η₀ b η t Cb ε Kg CT CR Km weight hL hμ (zero_le_one.trans hθ) hθκ hκp
      hη₀ hbp hη hη1 ht ht1 hCb.le hε.le hKg hKgη (lt_of_lt_of_le zero_lt_one hCT) hCTc hT hJ hlen hgain
      hw hw1 hCR hCRcn hKm U V blocks normals index radialIndex fineIndex cms Cf 6 hcms hcms1
      (by norm_num) hCfa24 hCfaWide (by convert hCfi using 1; norm_num) hCfiWide hv hcms hβ z
    have hthird : 64*SmallGapLiftSupport.C*C^(J+2)*η₀*(cn/η^2)^(1/3:ℝ)*((J:ℝ)+1)^2*T+
        2*θ/(3*6)+72*ζ*η₀*((J:ℝ)+1)^2*T≤2*θ/9 := by
      convert hnum'.2.2.2 using 1 <;> dsimp only [wideThirdCoarse,wideThirdRadial] <;> ring
    exact ⟨hj.1.trans hnum'.2.1,hj.2.1.trans hthird,hj.2.2.1.trans hnum'.2.1,hj.2.2.2.trans hthird⟩

end Bilevel.ChiExtensionCalibration
