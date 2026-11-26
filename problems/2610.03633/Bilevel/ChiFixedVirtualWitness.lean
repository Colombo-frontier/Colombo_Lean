import Bilevel.ChiFixedVirtualPrimitive
import Bilevel.ChiFixedDepthMacroObjective
import Bilevel.ChiSourceDeterministicWitness

/-! A fixed-depth actual hard objective on the full accuracy window.
Its variation budget is `μ`; larger prescribed budgets are obtained by
`ChiPrimitive.enlargeVariation`. No information lower bound is assumed. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry ChiExtension ChiCurvatureSchedule ChiIndependentWidths ChiPrefixEvaluation
universe u

set_option maxHeartbeats 1200000 in
theorem fixed_virtual_deterministic_witness :
    ∃ t η ζ cn CR Km Cgap η₀ bStar Cf c : ℝ,
      0<t ∧ t<1 ∧ 0<η ∧ η≤1 ∧ 0<ζ ∧ ζ≤2/15 ∧ 0<cn ∧ cn≤1 ∧
      128≤cn/η^2 ∧ 1≤CR ∧ ζ*Real.sqrt cn≤CR ∧ 1≤Km ∧ 1≤Cgap ∧
      0<η₀ ∧ η₀≤1 ∧ 0<bStar ∧ bStar≤1 ∧ bStar^2≤1/(256*Cgap) ∧ 1≤Cf ∧ 0<c ∧ c≤1 ∧
    ∀ (E F : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      [FiniteDimensional ℝ F] (L μ κ Δ ε : ℝ),
      0<L → 0<μ → 2≤κ → κ=L/μ → 0<Δ → 0<ε → ε≤c*min L (Real.sqrt (L*Δ)) →
      let b := macroWidth bStar Δ (η₀*L)
      let h := middleWidth (32/t) ε (κ/6) (η₀*L) (t*η) 1
      let S := macroLength (1/(2*Cgap)) Δ (η₀*L) b
      let n := S-1
      let Kg := b/h
      let initial : Scale := ⟨η₀*L,b⟩
      64≤S ∧ n+1=S ∧ 64≤middleLength cn b h ∧ 0<h/b ∧ h/b≤η ∧
      cn*Δ/(8*Cgap*(η₀*L)*h^2)≤((S*middleLength cn b h:ℕ):ℝ) ∧
      ∀ (U : Space n →ₗᵢ[ℝ] E)
        (V : ∀ j,List ℕ → Space (sourceChainIndex cn (sourceRatio 1 j) (resolution η Kg j)) →ₗᵢ[ℝ] F),
      let M := sourceMacroNode n initial Km U
      let weight := fun j => t^(j+1)
      let D := sourceGeometry initial (sourceRatio 1) (resolution η Kg) weight 3 1 ζ cn CR V
      let rad := fun j => weight j*(D j []).nu
      let R := fun j => (D j []).radius
      let v := fineParameter μ (3*μ/2) ((D 1 []).ell) (normalCoefficient L 1) Cf 1
      ∃ hv : 1≤v, ∃ hwidth : ∀ j I,0<(D j I).width,
      let Ext := hierarchyExtension 2 M D 1 (1/128) v (by norm_num) (hwidth 1 []) hv 2
        (sourceCoarseNormal 1) (sourceRadialNormal 1) (sourceFineNormal 1 (by omega)) rad R (normalCoefficient L 1)
      let Ext₀ := hierarchyInactiveExtension 2 M D 1 (1/128) v (by norm_num) (hwidth 1 []) hv 2
        (sourceCoarseNormal 1) (sourceRadialNormal 1) (sourceFineNormal 1 (by omega)) rad R (normalCoefficient L 1)
      let hExt : ContDiff ℝ 3 Ext := hierarchyExtension_contDiff 2 M D 1 (1/128) v (by norm_num) (hwidth 1 []) hv 2
        (sourceCoarseNormal 1) (sourceRadialNormal 1) (sourceFineNormal 1 (by omega)) rad R (normalCoefficient L 1)
        (fun i => hwidth (i.val+1) [])
      ∃ hb : ∀ z,‖iteratedFDeriv ℝ 2 Ext z‖≤(1:ℝ)/12,
      (∀ z,‖iteratedFDeriv ℝ 2 Ext₀ z‖≤(1:ℝ)/12) ∧
      (∀ (rM : ℕ → ℕ) (r : ℕ → ℕ → List ℕ → ℕ) (active : Bool)
        (p : VirtualState M D),ValidState M D rM r p →
        let f := statePotential active 2 M D 1 rM r (1/128) v 2
          (sourceCoarseNormal 1) (sourceRadialNormal 1) (sourceFineNormal 1 (by omega)) rad R (normalCoefficient L 1) p
        ContDiff ℝ 3 f ∧ ∀ z,‖iteratedFDeriv ℝ 2 f z‖≤(1:ℝ)/12 ∧ ‖iteratedFDeriv ℝ 3 f z‖≤(2:ℝ)/9) ∧
      ∃ P : Model.Primitive (X:=Joint E (Blocks 2 F)) (Y:=Joint (Blocks 2 F) (Normals 2)) μ L L L μ,
      (∀ x y,P.f x y=hierarchyUpper 2 M (initial.curvature/24) D 1 rad R 2 (normalCoefficient L 1) x.fst y) ∧
      (∀ x y,P.g x y=extensionLower Ext hExt ⟨1/12,by norm_num⟩ hb
        (by change (1:ℝ)/12<1;norm_num) (3*μ/2) (L/4) x.fst x.snd y) ∧
      ∃ r : P.Response,r.y 0=0 ∧ Nonempty (P.GapCertificate r 0 Δ) ∧
        (∀ x,r.y x=pack ((κ/6) • x.snd) (normalTrace Ext x.fst ((κ/6) • x.snd))) ∧
        (∀ x,P.hyperobjective r x=jointOuter 2 M (initial.curvature/24) D rad R 1 (κ/6) x) ∧
        (∀ x y,P.IsLowerSolution x y ↔ y=r.y x) ∧ P.hyperobjective r 0=0 ∧
        ∀ x,M.coordinates x.fst (Fin.last n)<b → 8*ε≤‖gradient (P.hyperobjective r) x‖ := by
  obtain ⟨t,η,ζ,cn,CR,Km,Cgap,ht,ht1,hη,hη1,hζ,hζsmall,hcn,hcn1,hlen,hCR,hCRcn,hKm,hCgap,hmacro⟩ :=
    fixed_macro_objective_certificate.{u}
  have hCb : 0<32/t := by positivity
  have hζ1 : ζ≤1 := by linarith only [hζsmall]
  obtain ⟨η₀,Cf,cold,hη₀,hη₀1,hCf,hcold,_hcold1,hprimitive⟩ := fixed_virtual_primitive_certificate
    (A:=3) (Kminus:=1) (Cb:=32/t) (cms:=1/128) (by norm_num) (by norm_num)
    hζ hζ1 hcn hcn1 hη hη1 hlen hCR hCRcn hKm hCb ht ht1.le (by norm_num) (by norm_num)
  let bStar := 1/(256*Cgap+1)
  have hCg : 0<Cgap := by linarith only [hCgap]
  have hbs : 0<bStar := by dsimp [bStar]; positivity
  have hbs1 : bStar≤1 := by
    apply (div_le_one (by positivity : 0<256*Cgap+1)).mpr
    linarith only [hCg]
  have hbsgap : bStar^2≤1/(256*Cgap) := by
    have hh : bStar^2≤bStar := by nlinarith only [hbs,hbs1]
    exact hh.trans (one_div_le_one_div_of_le (by positivity) (by linarith : 256*Cgap≤256*Cgap+1))
  obtain ⟨c,hc,hc1,hccold,hobjective⟩ := hmacro η₀ bStar cold hη₀ hη₀1 hbs hbsgap hcold
  refine ⟨t,η,ζ,cn,CR,Km,Cgap,η₀,bStar,Cf,c,ht,ht1,hη,hη1,hζ,hζsmall,hcn,hcn1,hlen,
    hCR,hCRcn,hKm,hCgap,hη₀,hη₀1,hbs,hbs1,hbsgap,hCf,hc,hc1,?_⟩
  intro E F _ _ _ _ _ _ _ _ L μ κ Δ ε hL hμ hκ hκeq hΔ hε hacc
  dsimp only
  let b := macroWidth bStar Δ (η₀*L)
  let h := middleWidth (32/t) ε (κ/6) (η₀*L) (t*η) 1
  let S := macroLength (1/(2*Cgap)) Δ (η₀*L) b
  let n := S-1
  let Kg := b/h
  let initial : Scale := ⟨η₀*L,b⟩
  let weight := fun j : ℕ => t^(j+1)
  have ho := hobjective E F L Δ κ ε hL hΔ hκ hε hacc
  have hbp : 0<b := macroWidth_pos hbs hΔ (mul_pos hη₀ hL)
  have hb1 : b≤1 := (macroWidth_le hbs.le).trans hbs1
  have hKp : 0<κ/6 := by linarith only [hκ]
  have hhp : 0<h := by dsimp [h,middleWidth]; positivity
  have hKg : 0<Kg := div_pos hbp hhp
  have hKgη : 1/η≤Kg := by
    apply (div_le_iff₀ hη).mpr
    have hh := (div_le_iff₀ hbp).mp ho.2.2.2.2.1
    dsimp [Kg]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hhp).mpr
    nlinarith only [hh]
  have hgain : b/Kg=h := by dsimp [Kg]; field_simp
  have haccl : ε≤cold*L := hacc.trans ((mul_le_mul_of_nonneg_left (min_le_left _ _) hc.le).trans
    (mul_le_mul_of_nonneg_right hccold hL.le))
  have hp := hprimitive E F n L μ κ b ε Kg weight hL hμ hκ hκeq hbp hb1 hε.le haccl hKg hKgη hgain
    (fun j => pow_pos ht _) (fun j => pow_le_one₀ ht.le ht1.le)
  refine ⟨ho.1,ho.2.1,ho.2.2.1,ho.2.2.2.1,ho.2.2.2.2.1,ho.2.2.2.2.2.1,?_⟩
  intro U V
  let M := sourceMacroNode n initial Km U
  let D := sourceGeometry initial (sourceRatio 1) (resolution η Kg) weight 3 1 ζ cn CR V
  let rad := fun j => weight j*(D j []).nu
  let R := fun j => (D j []).radius
  let obj := jointOuter 2 M (initial.curvature/24) D rad R 1 (κ/6)
  obtain ⟨hv,hwidth,hp'⟩ := hp U V
  obtain ⟨hb,hi,hvirtual,P,hf,hg,r,hrzero,hr,hm,hu⟩ := hp' (sourceCoarseNormal 1) (sourceRadialNormal 1) (sourceFineNormal 1 (by omega))
  have ho' := ho.2.2.2.2.2.2 U V
  have hcont : Continuous obj := (jointOuter_contDiff 2 M (initial.curvature/24) D rad R 1 (κ/6) 0).continuous
  have hgap := ChiPrimitive.gapCertificate_of_coercive_mean P r obj hcont ho'.1 hm 0 Δ ho'.2.2.1
  refine ⟨hv,hwidth,hb,hi,hvirtual,P,hf,hg,r,hrzero,hgap,hr,hm,hu,?_,?_⟩
  · exact (hm 0).trans ho'.2.1
  · intro x hlast
    rw [ChiPrimitive.mean_gradient_eq P r obj hm x]
    exact ho'.2.2.2 x hlast

end Bilevel.ChiExtensionCalibration

