import Bilevel.ChiVirtualPrimitive
import Bilevel.ChiUniformMacroObjective
import Bilevel.ChiSourceDeterministicWitness

/-! One shared actual/virtual calibration with actual Primitive, unique response, prescribed initial gap and
blind gradient barrier on the full manuscript accuracy window. The raw
force constant is selected before all public budgets. Oracle information
and random-frame lower bounds are separate statements. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry ChiExtension ChiCurvatureSchedule ChiIndependentWidths ChiPrefixEvaluation
universe u

set_option maxHeartbeats 1000000 in
theorem wide_virtual_deterministic_witness (Braw : ℝ) (hBraw : 0≤Braw) :
    ∃ t η ζ cn CR Km Cgap η₀ bStar Cf CT c : ℝ,
      0<t ∧ t<1 ∧ 0<η ∧ η≤1 ∧ 0<ζ ∧ ζ≤2/15 ∧ 0<cn ∧ cn≤1 ∧
      128≤cn/η^2 ∧ 1≤CR ∧ ζ*Real.sqrt cn≤CR ∧ 1≤Km ∧ 1≤Cgap ∧
      0<η₀ ∧ η₀≤1 ∧ 0<bStar ∧ bStar≤1 ∧ bStar^2≤1/(256*Cgap) ∧
      1≤Cf ∧ 1≤CT ∧ 0<c ∧ c≤1 ∧
    ∀ (E F : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      [FiniteDimensional ℝ F] (L μ κ θ Δ ε : ℝ),
      0<L → 0<μ → 2≤κ → κ=L/μ → θ≤κ^2 → wideBranchThreshold CT≤θ →
      0<Δ → 0<ε → ε≤c*min L (Real.sqrt (L*Δ)) →
      let J := chosenDepth θ
      let T := scale θ CT 6
      let b := macroWidth bStar Δ (η₀*L)
      let h := middleWidth (32/t) ε (κ/6) (η₀*L) (t*η) J
      let S := macroLength (1/(2*Cgap)) Δ (η₀*L) b
      let n := S-1
      let Kg := b/h
      let initial : Scale := ⟨η₀*L,b⟩
      ∃ hJ : 1≤J,64≤S ∧ n+1=S ∧ 64≤middleLength cn b h ∧ 0<h/b ∧ h/b≤η ∧
      cn*Δ/(8*Cgap*(η₀*L)*h^2)≤((S*middleLength cn b h:ℕ):ℝ) ∧
      ∀ (U : Space n →ₗᵢ[ℝ] E)
        (V : ∀ j,List ℕ → Space (sourceChainIndex cn (sourceRatio T j) (resolution η Kg j)) →ₗᵢ[ℝ] F),
      let M : Node E := sourceMacroNode n initial Km U
      let weight := fun j => t^(j+1)
      let D : Geometry F := sourceGeometry initial (sourceRatio T) (resolution η Kg) weight 3 1 ζ cn CR V
      let rad := fun j => weight j*(D j []).nu
      let R := fun j => (D j []).radius
      let v : ℝ := fineParameter (θ*μ) (3*μ/2) ((D J []).ell) (normalCoefficient L J) Cf J
      ∃ hv : 1≤v, ∃ hwidth : ∀ j I,0<(D j I).width,
      2*SmallGapLiftSupport.C*Braw*(1/128)*(D J []).ell*((D J []).width)^2/
        (normalCoefficient L J*Real.sqrt v)≤(D J []).width/128 ∧
      let Ext := hierarchyExtension (J+1) M D J (1/128) v (by norm_num) (hwidth J []) hv (2*J)
        (sourceCoarseNormal J) (sourceRadialNormal J) (sourceFineNormal J hJ) rad R (normalCoefficient L J)
      let Ext₀ := hierarchyInactiveExtension (J+1) M D J (1/128) v (by norm_num) (hwidth J []) hv (2*J)
        (sourceCoarseNormal J) (sourceRadialNormal J) (sourceFineNormal J hJ) rad R (normalCoefficient L J)
      let hExt : ContDiff ℝ 3 Ext := hierarchyExtension_contDiff (J+1) M D J (1/128) v (by norm_num) (hwidth J []) hv (2*J)
        (sourceCoarseNormal J) (sourceRadialNormal J) (sourceFineNormal J hJ) rad R (normalCoefficient L J)
        (fun i => hwidth (i.val+1) [])
      ∃ hb : ∀ z,‖iteratedFDeriv ℝ 2 Ext z‖≤(1:ℝ)/12,
      (∀ z,‖iteratedFDeriv ℝ 2 Ext₀ z‖≤(1:ℝ)/12) ∧
      (∀ (rM : ℕ → ℕ) (r : ℕ → ℕ → List ℕ → ℕ) (active : Bool)
        (p : VirtualState M D),ValidState M D rM r p →
        let f := statePotential active (J+1) M D J rM r (1/128) v (2*J)
          (sourceCoarseNormal J) (sourceRadialNormal J) (sourceFineNormal J hJ) rad R (normalCoefficient L J) p
        ContDiff ℝ 3 f ∧ ∀ z,‖iteratedFDeriv ℝ 2 f z‖≤1/12 ∧ ‖iteratedFDeriv ℝ 3 f z‖≤2*θ/9) ∧
      ∃ P : Model.Primitive (X:=Joint E (Blocks (J+1) F)) (Y:=Joint (Blocks (J+1) F) (Normals (2*J))) μ L L L (θ*μ),
      (∀ x y,P.f x y=hierarchyUpper (J+1) M (initial.curvature/24) D J rad R (2*J) (normalCoefficient L J) x.fst y) ∧
      (∀ x y,P.g x y=extensionLower Ext hExt ⟨1/12,by norm_num⟩ hb
        (by change (1:ℝ)/12<1;norm_num) (3*μ/2) (L/4) x.fst x.snd y) ∧
      ∃ r : P.Response,r.y 0=0 ∧ Nonempty (P.GapCertificate r 0 Δ) ∧
        (∀ x,r.y x=pack ((κ/6) • x.snd) (normalTrace Ext x.fst ((κ/6) • x.snd))) ∧
        (∀ x,P.hyperobjective r x=jointOuter (J+1) M (initial.curvature/24) D rad R J (κ/6) x) ∧
        (∀ x y,P.IsLowerSolution x y ↔ y=r.y x) ∧ P.hyperobjective r 0=0 ∧
        ∀ x,M.coordinates x.fst (Fin.last n)<b → 8*ε≤‖gradient (P.hyperobjective r) x‖ := by
  obtain ⟨t,η,ζ,cn,CR,Km,Cgap,ht,ht1,hη,hη1,hζ,hζsmall,hcn,hcn1,hlen,hCR,hCRcn,hKm,hCgap,hmacro⟩ :=
    uniform_macro_objective_certificate.{u}
  have hCb : 0<32/t := by positivity
  have hζ1 : ζ≤1 := by linarith only [hζsmall]
  obtain ⟨η₀,bStar,hη₀,hη₀1,hbs,hbs1,hbsgap,hprimitive⟩ :=
    wide_virtual_primitive_certificate (A:=3) (Kminus:=1) (Cb:=32/t) (cms:=1/128)
      (by norm_num) (by norm_num) hζ hζ1 hcn hcn1 hη hη1 hlen hCR hCRcn hKm hCgap
      hCb ht ht1.le (by norm_num) (by norm_num) hBraw
  obtain ⟨cold,hcold,_hcold1,hobjective⟩ := hmacro η₀ bStar hη₀ hη₀1 hbs hbsgap
  obtain ⟨Cf,CT,c,hCf,hCT,hc,hc1,hccold,hprimitive⟩ := hprimitive cold hcold
  refine ⟨t,η,ζ,cn,CR,Km,Cgap,η₀,bStar,Cf,CT,c,ht,ht1,hη,hη1,hζ,hζsmall,hcn,hcn1,hlen,
    hCR,hCRcn,hKm,hCgap,hη₀,hη₀1,hbs,hbs1,hbsgap,hCf,hCT,hc,hc1,?_⟩
  intro E F _ _ _ _ _ _ _ _ L μ κ θ Δ ε hL hμ hκ hκeq hθκ hbranch hΔ hε hacc
  dsimp only
  let J := chosenDepth θ
  let T := scale θ CT 6
  let b := macroWidth bStar Δ (η₀*L)
  let h := middleWidth (32/t) ε (κ/6) (η₀*L) (t*η) J
  let S := macroLength (1/(2*Cgap)) Δ (η₀*L) b
  let n := S-1
  let Kg := b/h
  let initial : Scale := ⟨η₀*L,b⟩
  let weight := fun j : ℕ => t^(j+1)
  have hbranches := wide_branch_conditions hCT hbranch
  have hJ : 1≤J := hbranches.2.1
  have hT : 1≤T := (by norm_num : (1:ℝ)≤2).trans hbranches.2.2
  have haccold : ε≤cold*min L (Real.sqrt (L*Δ)) := hacc.trans
    (mul_le_mul_of_nonneg_right hccold (le_min hL.le (Real.sqrt_nonneg _)))
  have ho := hobjective E F L Δ κ θ ε T hL hΔ hκ hbranches.1 hθκ hε hT haccold
  have hp := hprimitive E F n L μ κ θ Δ ε weight hL hμ hκ hκeq hθκ hbranch hΔ hε hacc
    (fun j => pow_pos ht _) (fun j => pow_le_one₀ ht.le ht1.le)
  refine ⟨hJ,ho.1,ho.2.1,ho.2.2.1,ho.2.2.2.1,ho.2.2.2.2.1,ho.2.2.2.2.2.1,?_⟩
  intro U V
  let M : Node E := sourceMacroNode n initial Km U
  let D : Geometry F := sourceGeometry initial (sourceRatio T) (resolution η Kg) weight 3 1 ζ cn CR V
  let rad := fun j => weight j*(D j []).nu
  let R := fun j => (D j []).radius
  let obj := jointOuter (J+1) M (initial.curvature/24) D rad R J (κ/6)
  obtain ⟨hv,hwidth,hforce,hp'⟩ := hp U V
  obtain ⟨hb,hi,hvirtual,P,hf,hg,r,hrzero,hr,hm,hu⟩ := hp' (sourceCoarseNormal J) (sourceRadialNormal J) (sourceFineNormal J hJ)
  have ho' := ho.2.2.2.2.2.2 U V
  have hcont : Continuous obj := (jointOuter_contDiff (J+1) M (initial.curvature/24) D rad R J (κ/6) 0).continuous
  have hgap := ChiPrimitive.gapCertificate_of_coercive_mean P r obj hcont ho'.1 hm 0 Δ ho'.2.2.1
  refine ⟨hv,hwidth,hforce,hb,hi,hvirtual,P,hf,hg,r,hrzero,hgap,hr,hm,hu,?_,?_⟩
  · exact (hm 0).trans ho'.2.1
  · intro x hlast
    rw [ChiPrimitive.mean_gradient_eq P r obj hm x]
    exact ho'.2.2.2 x hlast

end Bilevel.ChiExtensionCalibration
