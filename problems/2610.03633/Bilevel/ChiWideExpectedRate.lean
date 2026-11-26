import Bilevel.ChiWideExpectedWitness
import Bilevel.ChiExpectedRateProperty
import Bilevel.ChiSourceCapacity
import Bilevel.ChiUniformActualProbabilityRate
import Bilevel.ChiCertifiedDimension
import Bilevel.ChiPublicSignal
import Bilevel.ChiCanonicalQueryCertificate
import Bilevel.ChiCanonicalPublicData

/-! The actual full-window Primitive, gap, unique response and conservative
full-query SFO share all construction constants. The informative envelope
retains the finest normal width. No information lower bound is assumed. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry ChiExtension ChiCurvatureSchedule ChiIndependentWidths ChiPrefixEvaluation ChiHierarchyHaar ChiTreeProgress
universe u

set_option maxHeartbeats 1200000 in
theorem wide_expected_rate_witness (Braw : ℝ) (hBraw : 0≤Braw) :
    ∃ t η ζ cn CR Km Cgap η₀ bStar Cf CT c Bs : ℝ,
      0<t ∧ t<1 ∧ 0<η ∧ η≤1 ∧ 0<ζ ∧ ζ≤2/15 ∧ 0<cn ∧ cn≤1 ∧
      128≤cn/η^2 ∧ 1≤CR ∧ ζ*Real.sqrt cn≤CR ∧ 1≤Km ∧ 1≤Cgap ∧
      0<η₀ ∧ η₀≤1 ∧ 0<bStar ∧ bStar≤1 ∧ bStar^2≤1/(256*Cgap) ∧
      1≤Cf ∧ 1≤CT ∧ 0<c ∧ c≤1 ∧ 1≤Bs ∧
    ∃ cRate : ℝ,0<cRate ∧ ∃ q : ℕ,
    ∀ (L μ κ θ Δ ε σg : ℝ),
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
      let weight := fun j => t^(j+1)
      let rad := sourcePublicRadialWeight initial (sourceRatio T) (resolution η Kg) weight ζ
      let R := sourcePublicNodeRadius initial (sourceRatio T) (resolution η Kg) weight CR ζ
      let v := sourcePublicFineParameter initial (sourceRatio T) (resolution η Kg) J (θ*μ) μ L Cf
      let B := sourcePublicAmplitude initial (sourceRatio T) (resolution η Kg) J (1/128) v μ L Bs
      ∃ hB : 0<B,
      ∃ (dim : ℕ),
      ∃ (hdim : ∀ j,sourceChainIndex cn (sourceRatio T j) (resolution η Kg j)+1≤dim),
      ∃ (hAll : ∀ i : ChiHierarchyIndex.FrameIndex (sourceCounts n cn (sourceRatio T) (resolution η Kg)) J,
          ChiHierarchyIndex.chainSize i+1≤dim),
      ∃ hJ : 1≤J,64≤S ∧ n+1=S ∧ 64≤middleLength cn b h ∧ 0<h/b ∧ h/b≤η ∧
      cn*Δ/(8*Cgap*(η₀*L)*h^2)≤((S*middleLength cn b h:ℕ):ℝ) ∧
      ∃ H : CanonicalQueryCertificate n J dim cn (sourceRatio T) (resolution η Kg) hdim hAll
        initial weight ζ CR Km hJ v rad R L (κ/6) ε,
      H.RateProperty μ (BernoulliOracle.probability B σg) (BernoulliOracle.probability_le_one hB)
        (cRate*(L*(1+θ)*κ^2*Δ/ε^2+L^3*θ^2*(1+θ)*κ^8*σg^2*Δ/ε^6)/(Real.log (2+θ))^q) ∧
      ∀ a : Orientations (sourceCounts n cn (sourceRatio T) (resolution η Kg)) J dim,
      let M : Node (EuclideanGaussian.Space dim) := sourceCanonicalMacro n J dim cn (sourceRatio T) (resolution η Kg) hAll a initial Km

      let D : Geometry (EuclideanGaussian.Space dim) := sourceCanonicalGeometry n J dim cn (sourceRatio T) (resolution η Kg) hdim a initial weight 3 1 ζ CR



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
      ∃ P : Model.Primitive (X:=Joint (EuclideanGaussian.Space dim) (Blocks (J+1) (EuclideanGaussian.Space dim))) (Y:=Joint (Blocks (J+1) (EuclideanGaussian.Space dim)) (Normals (2*J))) μ L L L (θ*μ),
      (∀ x y,P.f x y=hierarchyUpper (J+1) M (initial.curvature/24) D J rad R (2*J) (normalCoefficient L J) x.fst y) ∧
      (∀ x y,P.g x y=extensionLower Ext hExt ⟨1/12,by norm_num⟩ hb
        (by change (1:ℝ)/12<1;norm_num) (3*μ/2) (L/4) x.fst x.snd y) ∧
      ∃ r : P.Response,r.y 0=0 ∧ Nonempty (P.GapCertificate r 0 Δ) ∧
        (∀ x,r.y x=pack ((κ/6) • x.snd) (normalTrace Ext x.fst ((κ/6) • x.snd))) ∧
        (∀ x,P.hyperobjective r x=jointOuter (J+1) M (initial.curvature/24) D rad R J (κ/6) x) ∧
        (∀ x y,P.IsLowerSolution x y ↔ y=r.y x) ∧ P.hyperobjective r 0=0 ∧
        (∀ x,M.coordinates x.fst (Fin.last n)<b → 8*ε≤‖gradient (P.hyperobjective r) x‖) ∧
        let W := sourcePublicFinestWidth initial (sourceRatio T) (resolution η Kg) J (1/128) v
        let ηsig := 2*SmallGapLiftSupport.C*Bs^(J+2)*sourcePublicEll initial (sourceRatio T) (resolution η Kg) J*sourcePublicWidth initial (sourceRatio T) (resolution η Kg) J*W/normalCoefficient L J
        let hExt₀ : ContDiff ℝ 3 Ext₀ := hierarchyInactiveExtension_contDiff (J+1) M D J (1/128) v (by norm_num) (hwidth J []) hv (2*J)
          (sourceCoarseNormal J) (sourceRadialNormal J) (sourceFineNormal J hJ) rad R (normalCoefficient L J)
          (fun i => hwidth (i.val+1) [])
        ∃ hi : ∀ z,‖iteratedFDeriv ℝ 2 Ext₀ z‖≤(1:ℝ)/4,
        (∀ z,‖iteratedFDeriv ℝ 1 (fun q => Ext q-Ext₀ q) z‖≤ηsig) ∧
        let g := fullExtensionLower Ext hExt ⟨1/12,by norm_num⟩ hb (by change (1:ℝ)/12<1;norm_num) μ L
        let g₀ := fullExtensionLower Ext₀ hExt₀ ⟨1/4,by norm_num⟩ hi (by change (1:ℝ)/4<1;norm_num) μ L
        ChiPrimitive.HasConservativeOracle P g g₀ (4*μ*ηsig) := by
  obtain ⟨t,η,ζ,cn,CR,Km,Cgap,η₀,bStar,Cf,CT,cold,Bs,ht,ht1,hη,hη1,hζ,hζsmall,hcn,hcn1,hlen,hCR,hCRcn,hKm,hCgap,hη₀,hη₀1,hbs,hbs1,hbsgap,hCf,hCT,hcold,hcold1,hBs,hmain⟩ := wide_expected_stochastic_witness Braw hBraw
  have hCb : 0<(32:ℝ)/t := by positivity
  have hCg : 0<Cgap := zero_lt_one.trans_le hCgap
  have hmacro : bStar^2≤(1/(2*Cgap))/128 := by
    convert hbsgap using 1
    ring
  obtain ⟨c,cN,hc,hc1,hccold,hcN,q,hrate⟩ := uniform_actual_probability_rate
    (by positivity : 0<(1:ℝ)/(2*Cgap)) hcn hη₀ hη₀1 hbs hCb ht hη hCT hlen hmacro hcold
    (zero_lt_one.trans_le hBs) (zero_lt_one.trans_le hCf) (by norm_num : 0<(1:ℝ)/128)
  refine ⟨t,η,ζ,cn,CR,Km,Cgap,η₀,bStar,Cf,CT,c,Bs,ht,ht1,hη,hη1,hζ,hζsmall,hcn,hcn1,hlen,hCR,hCRcn,hKm,hCgap,hη₀,hη₀1,hbs,hbs1,hbsgap,hCf,hCT,hc,hc1,hBs,cN/512,by positivity,q,?_⟩
  intro L μ κ θ Δ ε σg hL hμ hκ hκeq hθκ hbranch hΔ hε hacc
  have haccold := hacc.trans (mul_le_mul_of_nonneg_right hccold
    (le_min hL.le (Real.sqrt_nonneg _)))
  obtain ⟨hB,dim,hdim,hAll,hJ,hS,hn,hn₀,hrp,hratio,hcount,H,hExpected,hd⟩ :=
    hmain L μ κ θ Δ ε σg hL hμ hκ hκeq hθκ hbranch hΔ hε haccold
  dsimp only
  let J := chosenDepth θ
  let T := scale θ CT 6
  let b := macroWidth bStar Δ (η₀*L)
  let h := middleWidth (32/t) ε (κ/6) (η₀*L) (t*η) J
  let initial : Scale := ⟨η₀*L,b⟩
  let weight := fun j => t^(j+1)
  have hT : 1≤T := (by have hh := (wide_branch_conditions hCT hbranch).2.2; exact le_trans (by norm_num) hh)
  have hb : 0<b := macroWidth_pos hbs hΔ (mul_pos hη₀ hL)
  have hh : 0<h := by
    have hp : 0<h/b := hrp
    simpa only [div_mul_cancel₀ _ hb.ne'] using mul_pos hp hb
  have hκp : 0<κ := zero_lt_two.trans_le hκ
  obtain ⟨hSr,hmr,hr⟩ := hrate (EuclideanGaussian.Space dim) L Δ μ κ θ ε σg 3 1 ζ CR weight
    hL hΔ hμ hκ hκeq (wide_branch_conditions hCT hbranch).1 hθκ hε hT hacc
  have hrate' := hr (canonicalFamily (counts:=sourceCounts (macroLength (1/(2*Cgap)) Δ (η₀*L) b-1) cn (sourceRatio T) (resolution η (b/h))) (J:=J) (D:=dim) hdim (fun _ => 1)) hJ H.fine_ge_one
  let v := sourcePublicFineParameter initial (sourceRatio T) (resolution η (b/h)) J (θ*μ) μ L Cf
  let B := sourcePublicAmplitude initial (sourceRatio T) (resolution η (b/h)) J (1/128) v μ L Bs
  let N := activationCount (1/(2*Cgap)) cn Δ (η₀*L) b h η T J
  let rateBase := L*(1+θ)*κ^2*Δ/ε^2+L^3*θ^2*(1+θ)*κ^8*σg^2*Δ/ε^6
  change cN*rateBase/(Real.log (2+θ))^q≤(N:ℝ)*(BernoulliOracle.probability B σg)⁻¹ at hrate'
  have hcap := source_capacity_activation hcn.le hb hh hT hlen
    (show 1≤macroLength (1/(2*Cgap)) Δ (η₀*L) b from (by norm_num : (1:ℕ)≤64).trans hS)
    (show 1≤middleLength cn b h from (by norm_num : (1:ℕ)≤64).trans hn₀) J
  refine ⟨hB,dim,hdim,hAll,hJ,hS,hn,hn₀,hrp,hratio,hcount,H,?_,hd⟩
  apply CanonicalQueryCertificate.ExpectedProperty.rate H hExpected
  rw [hcap]
  change (cN/512)*rateBase/(Real.log (2+θ))^q≤(N:ℝ)/(512*BernoulliOracle.probability B σg)
  have hr512 := div_le_div_of_nonneg_right hrate' (by norm_num : (0:ℝ)≤512)
  convert hr512 using 1 <;> ring

end Bilevel.ChiExtensionCalibration
