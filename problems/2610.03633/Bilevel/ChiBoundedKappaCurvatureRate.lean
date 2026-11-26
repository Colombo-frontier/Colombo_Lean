import Bilevel.ChiBoundedThetaFullOracleRate
import Bilevel.ChiFixedSourceCurvature
import Bilevel.ChiCertifiedOracleProperty

/-! The actual bounded-condition-number family on the full all-gap window,
with explicit curvature and the same complete conservative SFO execution. -/
noncomputable section
set_option autoImplicit false
namespace Bilevel.ChiExtensionCalibration
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry ChiExtension ChiCurvatureSchedule ChiIndependentWidths ChiPrefixEvaluation ChiHierarchyHaar ChiTreeProgress
universe u

set_option maxHeartbeats 1200000 in
theorem bounded_kappa_curvature_rate_witness (Θ : ℝ) (hΘ : 2≤Θ) :
    ∃ t η ζ cn CR Km Cgap η₀ bStar Cf c Bs Ccurv : ℝ,
      0<t ∧ t<1 ∧ 0<η ∧ η≤1 ∧ 0<ζ ∧ ζ≤2/15 ∧ 0<cn ∧ cn≤1 ∧
      128≤cn/η^2 ∧ 1≤CR ∧ ζ*Real.sqrt cn≤CR ∧ 1≤Km ∧ 1≤Cgap ∧
      0<η₀ ∧ η₀≤1 ∧ 0<bStar ∧ bStar≤1 ∧ bStar^2≤1/(256*Cgap) ∧
      1≤Cf ∧ 0<c ∧ c≤1 ∧ 1≤Bs ∧ 1≤Ccurv ∧
    ∃ cRate : ℝ,0<cRate ∧ 
    ∀ (L μ κ θ Δ ε σg : ℝ),
      0<L → 0<μ → 2≤κ → κ=L/μ → κ≤Θ → 1≤θ → θ≤κ →
      0<Δ → 0<ε → ε≤c*min L (κ*Real.sqrt (L*Δ)) →
      let J := (1:ℕ)
      let T := (1:ℝ)
      let b := macroWidth bStar Δ (η₀*L)
      let h := middleWidth (32/t) ε (κ/6) (η₀*L) (t*η) J
      let S := macroLength (1/(2*Cgap)) Δ (η₀*L) b
      let n := S-1
      let Kg := b/h
      let initial : Scale := ⟨η₀*L,b⟩
      let weight := fun j => t^(j+1)
      let rad := sourcePublicRadialWeight initial (sourceRatio T) (resolution η Kg) weight ζ
      let R := sourcePublicNodeRadius initial (sourceRatio T) (resolution η Kg) weight CR ζ
      let v := sourcePublicFineParameter initial (sourceRatio T) (resolution η Kg) J μ μ L Cf
      let B := sourcePublicAmplitude initial (sourceRatio T) (resolution η Kg) J (1/128) v μ L Bs
      ∃ hB : 0<B,
      ∃ (dim : ℕ),
      ∃ (hdim : ∀ j,sourceChainIndex cn (sourceRatio T j) (resolution η Kg j)+1≤dim),
      ∃ (hAll : ∀ i : ChiHierarchyIndex.FrameIndex (sourceCounts n cn (sourceRatio T) (resolution η Kg)) J,
          ChiHierarchyIndex.chainSize i+1≤dim),
      64≤S ∧ n+1=S ∧ 64≤middleLength cn b h ∧ 0<h/b ∧ h/b≤η ∧
      cn*Δ/(8*Cgap*(η₀*L)*h^2)≤((S*middleLength cn b h:ℕ):ℝ) ∧
      ∃ H : CanonicalQueryCertificate n J dim cn (sourceRatio T) (resolution η Kg) hdim hAll
        initial weight ζ CR Km (by norm_num) v rad R L (κ/6) ε,
      H.RateProperty μ (BernoulliOracle.probability B σg) (BernoulliOracle.probability_le_one hB)
        (cRate*(L*(1+θ)*κ^2*Δ/ε^2+L^3*θ^2*(1+θ)*κ^8*σg^2*Δ/ε^6)) ∧
      ∀ a : Orientations (sourceCounts n cn (sourceRatio T) (resolution η Kg)) J dim,
      let M : Node (EuclideanGaussian.Space dim) := sourceCanonicalMacro n J dim cn (sourceRatio T) (resolution η Kg) hAll a initial Km

      let D : Geometry (EuclideanGaussian.Space dim) := sourceCanonicalGeometry n J dim cn (sourceRatio T) (resolution η Kg) hdim a initial weight 3 1 ζ CR



      ∃ hv : 1≤v, ∃ hwidth : ∀ j I,0<(D j I).width,
      let Ext := hierarchyExtension (J+1) M D J (1/128) v (by norm_num) (hwidth J []) hv (2*J)
        (sourceCoarseNormal J) (sourceRadialNormal J) (sourceFineNormal J (by norm_num)) rad R (normalCoefficient L J)
      let Ext₀ := hierarchyInactiveExtension (J+1) M D J (1/128) v (by norm_num) (hwidth J []) hv (2*J)
        (sourceCoarseNormal J) (sourceRadialNormal J) (sourceFineNormal J (by norm_num)) rad R (normalCoefficient L J)
      let hExt : ContDiff ℝ 3 Ext := hierarchyExtension_contDiff (J+1) M D J (1/128) v (by norm_num) (hwidth J []) hv (2*J)
        (sourceCoarseNormal J) (sourceRadialNormal J) (sourceFineNormal J (by norm_num)) rad R (normalCoefficient L J)
        (fun i => hwidth (i.val+1) [])
      ∃ hb : ∀ z,‖iteratedFDeriv ℝ 2 Ext z‖≤(1:ℝ)/12,
      (∀ z,‖iteratedFDeriv ℝ 2 Ext₀ z‖≤(1:ℝ)/12) ∧
      (∀ (rM : ℕ → ℕ) (r : ℕ → ℕ → List ℕ → ℕ) (active : Bool)
        (p : VirtualState M D),ValidState M D rM r p →
        let f := statePotential active (J+1) M D J rM r (1/128) v (2*J)
          (sourceCoarseNormal J) (sourceRadialNormal J) (sourceFineNormal J (by norm_num)) rad R (normalCoefficient L J) p
        ContDiff ℝ 3 f ∧ ∀ z,‖iteratedFDeriv ℝ 2 f z‖≤(1:ℝ)/12 ∧ ‖iteratedFDeriv ℝ 3 f z‖≤(2:ℝ)/9) ∧
      ∃ P : Model.Primitive (X:=Joint (EuclideanGaussian.Space dim) (Blocks (J+1) (EuclideanGaussian.Space dim))) (Y:=Joint (Blocks (J+1) (EuclideanGaussian.Space dim)) (Normals (2*J))) μ L L L (θ*μ),
      (∀ x y,P.f x y=hierarchyUpper (J+1) M (initial.curvature/24) D J rad R (2*J) (normalCoefficient L J) x.fst y) ∧
      (∀ x y,P.g x y=extensionLower Ext hExt ⟨1/12,by norm_num⟩ hb
        (by change (1:ℝ)/12<1;norm_num) (3*μ/2) (L/4) x.fst x.snd y) ∧
      ∃ r : P.Response,r.y 0=0 ∧ Nonempty (P.GapCertificate r 0 Δ) ∧
        (∀ x,r.y x=pack ((κ/6) • x.snd) (normalTrace Ext x.fst ((κ/6) • x.snd))) ∧
        (∀ x,P.hyperobjective r x=jointOuter (J+1) M (initial.curvature/24) D rad R J (κ/6) x) ∧
        (∀ x y,P.IsLowerSolution x y ↔ y=r.y x) ∧ P.hyperobjective r 0=0 ∧
        (∀ x,M.coordinates x.fst (Fin.last n)<b → 8*ε≤‖gradient (P.hyperobjective r) x‖) ∧
        (∀ x z,‖gradient (P.hyperobjective r) x-gradient (P.hyperobjective r) z‖≤
          (Ccurv*L*κ^2)*‖x-z‖) ∧
        let W := sourcePublicFinestWidth initial (sourceRatio T) (resolution η Kg) J (1/128) v
        let ηsig := 2*SmallGapLiftSupport.C*Bs^(J+2)*sourcePublicEll initial (sourceRatio T) (resolution η Kg) J*sourcePublicWidth initial (sourceRatio T) (resolution η Kg) J*W/normalCoefficient L J
        let hExt₀ : ContDiff ℝ 3 Ext₀ := hierarchyInactiveExtension_contDiff (J+1) M D J (1/128) v (by norm_num) (hwidth J []) hv (2*J)
          (sourceCoarseNormal J) (sourceRadialNormal J) (sourceFineNormal J (by norm_num)) rad R (normalCoefficient L J)
          (fun i => hwidth (i.val+1) [])
        ∃ hi : ∀ z,‖iteratedFDeriv ℝ 2 Ext₀ z‖≤(1:ℝ)/4,
        (∀ z,‖iteratedFDeriv ℝ 1 (fun q => Ext q-Ext₀ q) z‖≤ηsig) ∧
        let g := fullExtensionLower Ext hExt ⟨1/12,by norm_num⟩ hb (by change (1:ℝ)/12<1;norm_num) μ L
        let g₀ := fullExtensionLower Ext₀ hExt₀ ⟨1/4,by norm_num⟩ hi (by change (1:ℝ)/4<1;norm_num) μ L
        ChiPrimitive.HasConservativeOracle P g g₀ (4*μ*ηsig) ∧
        H.HasFullOracle μ (θ*μ) B a P := by
  have hΘ1 : 1≤Θ := by linarith
  have hΘp : 0<Θ := by linarith
  obtain ⟨t,η,ζ,cn,CR,Km,Cgap,η₀,bStar,Cf,c,Bs,ht,ht1,hη,hη1,hζ,hζsmall,hcn,hcn1,hlen,hCR,hCRcn,hKm,hCgap,hη₀,hη₀1,hbs,hbs1,hbsgap,hCf,hc,hc1,hBs,cRate,hcRate,hmain⟩ :=
    bounded_theta_full_oracle_rate_witness Θ hΘ1
  obtain ⟨Ccurv,hCcurv,hcurvature⟩ := source_fixed_public_curvature 3 1 ζ cn CR Km η t
    (by norm_num) (by norm_num) hζ (by linarith only [hζsmall]) hcn hcn1 hCR hCRcn hKm hη hη1 hlen ht ht1.le
  have hcΘ : 0<c/Θ := div_pos hc hΘp
  have hcΘ1 : c/Θ≤1 := (div_le_one hΘp).mpr (hc1.trans hΘ1)
  refine ⟨t,η,ζ,cn,CR,Km,Cgap,η₀,bStar,Cf,c/Θ,Bs,Ccurv,ht,ht1,hη,hη1,hζ,hζsmall,hcn,hcn1,hlen,hCR,hCRcn,hKm,hCgap,hη₀,hη₀1,hbs,hbs1,hbsgap,hCf,hcΘ,hcΘ1,hBs,hCcurv,cRate,hcRate,?_⟩
  intro L μ κ θ Δ ε σg hL hμ hκ hκeq hκΘ hθ hθκ hΔ hε hacc
  dsimp only
  have hacc' := bounded_kappa_accuracy_window hc.le hΘ1 hκΘ hL.le hacc
  obtain ⟨hB,dim,hdim,hAll,hS,hn,hn₀,hrp,hratio,hcount,H,hRate,hd⟩ :=
    hmain L μ κ θ Δ ε σg hL hμ hκ hκeq hθ (hθκ.trans hκΘ) hΔ hε hacc'
  refine ⟨hB,dim,hdim,hAll,hS,hn,hn₀,hrp,hratio,hcount,H,hRate,?_⟩
  intro a
  obtain ⟨hv,hw,hb,hi12,hvir,P,hf,hg,r,hr0,hgap,hresponse,hmean,hunique,hzero,hbarrier,hi,hsig,hO,hFull⟩ := hd a
  refine ⟨hv,hw,hb,hi12,hvir,P,hf,hg,r,hr0,hgap,hresponse,hmean,hunique,hzero,hbarrier,?_,hi,hsig,hO,hFull⟩
  let b := macroWidth bStar Δ (η₀*L)
  let h := middleWidth (32/t) ε (κ/6) (η₀*L) (t*η) 1
  let S := macroLength (1/(2*Cgap)) Δ (η₀*L) b
  let n := S-1
  let Kg := b/h
  have hbp : 0<b := macroWidth_pos hbs hΔ (mul_pos hη₀ hL)
  have hKp : 0<κ/6 := by linarith
  have hhp : 0<h := by dsimp [h,middleWidth];positivity
  have hKg : 0<Kg := div_pos hbp hhp
  have hKgη : 1/η≤Kg := by
    apply (div_le_iff₀ hη).mpr
    have hh := (div_le_iff₀ hbp).mp hratio
    dsimp [Kg]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hhp).mpr
    nlinarith only [hh]
  have hh := hcurvature (EuclideanGaussian.Space dim) (EuclideanGaussian.Space dim) n L η₀ b κ Kg
    hL hη₀ hη₀1 hbp hκ hKg hKgη (frame hAll a (Sum.inl ())) (canonicalFamily hdim a) 2
  intro x z
  rw [ChiPrimitive.mean_gradient_eq P r _ hmean x,ChiPrimitive.mean_gradient_eq P r _ hmean z]
  exact hh x z

end Bilevel.ChiExtensionCalibration
