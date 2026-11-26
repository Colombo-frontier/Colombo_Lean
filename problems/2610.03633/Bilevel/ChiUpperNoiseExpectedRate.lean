import Bilevel.ChiUpperNoiseExpectedWitness
import Bilevel.ChiUpperNoiseRateProperty

/-! Actual upper-noise expected-query lower rate, with fixed public dimension
before algorithms and the same retained Primitive/SFO family. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.ChiUpperNoise
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry ChiExtensionCalibration
  PartialLegendre ChiHierarchyHaar ChiHierarchyIndex ChiTreeProgress ChiCurvatureSchedule

set_option maxHeartbeats 1000000 in
theorem upper_noise_expected_rate_witness : ∃ t η ζ cn CR Km Cgap C η₀ c : ℝ,
    0<t ∧ t<1 ∧ 0<η ∧ η≤1 ∧ 0<ζ ∧ ζ≤2/15 ∧ 0<cn ∧ cn≤1 ∧
    128≤cn/η^2 ∧ 1≤CR ∧ ζ*Real.sqrt cn≤CR ∧ 1≤Km ∧ 1≤Cgap ∧ 1≤C ∧
    0<η₀ ∧ η₀≤1 ∧ 0<c ∧ c≤1 ∧
    ∃ cRate : ℝ,0<cRate ∧
    ∀ (L μ κ Δ ε ρg σf : ℝ),0<L → 0<μ → 2≤κ → κ=L/μ → 0<Δ → 0<ε → 0≤ρg →
      ε≤c*min L (Real.sqrt (L*Δ)) →
      let K := κ/6
      let Kg := max K (1/η)
      let ℓ := η₀*L
      let b := baseWidth (96/(t*η)) ε η₀ L
      let sc : Scale := ⟨ℓ,b⟩
      let n := macroIndex Δ Cgap (ℓ*b^2)
      let weight := fun j => t^(j+1)
      let rad := sourcePublicRadialWeight sc (fun _ => 1) (resolution η Kg) weight ζ
      let R := sourcePublicNodeRadius sc (fun _ => 1) (resolution η Kg) weight CR ζ
      let B := C*(96/(t*η))*ε/K
      ∃ hB : 0<B,
      ∃ (dim : ℕ),
      ∃ (hdim : ∀ j,sourceChainIndex cn 1 (resolution η Kg j)+1≤dim),
      ∃ (hAll : ∀ i : FrameIndex (sourceCounts n cn (fun _ => 1) (resolution η Kg)) 0,chainSize i+1≤dim),
      128≤n ∧ η₀*L*Δ/(4*Cgap*(96/(t*η))^2*ε^2)≤(n:ℝ) ∧
      128≤microLength cn Kg ∧ sourceChainIndex cn 1 (1/Kg)+1=microLength cn Kg ∧
      UpperNoiseRateProperty n dim cn (fun _ => 1) (resolution η Kg) hdim hAll sc weight ζ CR Km rad R K ε μ L
        (BernoulliOracle.probability B σf) (BernoulliOracle.probability_le_one hB)
        (cRate*(L*κ^2*Δ/ε^2+L*κ^4*σf^2*Δ/ε^4)) ∧
      ∀ a : Orientations (sourceCounts n cn (fun _ => 1) (resolution η Kg)) 0 dim,
      let M := sourceCanonicalMacro n 0 dim cn (fun _ => 1) (resolution η Kg) hAll a sc Km
      let D := sourceCanonicalGeometry n 0 dim cn (fun _ => 1) (resolution η Kg) hdim a sc weight 3 1 ζ CR
      ∃ P : Model.Primitive (X:=Joint (EuclideanGaussian.Space dim) (Blocks 1 (EuclideanGaussian.Space dim)))
          (Y:=Blocks 1 (EuclideanGaussian.Space dim)) μ L L L ρg,
        (∀ x u,P.f x u=core 1 M (ℓ/24) D rad R (pack x.fst u)) ∧
        (∀ x u,P.g x u=(3*μ/4)*‖u‖^2-(L/4)*⟪x.snd,u⟫) ∧
        (∀ x u,P.gy x u=(3*μ/2) • u-(L/4) • x.snd) ∧
        (∀ x u,P.gyy x u=(3*μ/2) • ContinuousLinearMap.id ℝ (Blocks 1 (EuclideanGaussian.Space dim))) ∧
        ∃ r : P.Response,(∀ x,r.y x=K • x.snd) ∧ r.y 0=0 ∧
          Nonempty (P.GapCertificate r 0 Δ) ∧
          (∀ x,P.hyperobjective r x=jointOuter 1 M (ℓ/24) D rad R 0 K x) ∧
          P.hyperobjective r 0=0 ∧
          (∀ z,M.coordinates z.fst (Fin.last n)<b → 8*ε≤‖gradient (P.hyperobjective r) z‖) ∧
          HasUpperNoiseOracle P (fullCore 1 M (ℓ/24) D rad R) (fullInactiveCore 1 M (ℓ/24) D rad R)
            (publicLower μ L) (C*(96/(t*η))*ε/K) := by
  obtain ⟨t,η,ζ,cn,CR,Km,Cgap,C,η₀,c,ht,ht1,hη,hη1,hζ,hζsmall,hcn,hcn1,hlen,hCR,hCRcn,hKm,hCgap,hC,
    hη₀,hη₀1,hc,hc1,hmain⟩ := upper_noise_expected_witness
  let Cb := (96:ℝ)/(t*η)
  let cRate := ((cn*η₀/(8*Cgap*Cb^2))/(1296*C^2*Cb^2))/512
  have hCg : 0<Cgap := zero_lt_one.trans_le hCgap
  have hC0 : 0<C := zero_lt_one.trans_le hC
  have hCb0 : 0<Cb := by dsimp [Cb]; positivity
  have hCb : 1≤Cb := by
    apply (le_div_iff₀ (mul_pos ht hη)).mpr
    have hh := mul_le_mul_of_nonneg_right ht1.le hη.le
    nlinarith only [hh,hη1]
  have hcRate : 0<cRate := by dsimp [cRate]; positivity
  refine ⟨t,η,ζ,cn,CR,Km,Cgap,C,η₀,c,ht,ht1,hη,hη1,hζ,hζsmall,hcn,hcn1,hlen,hCR,hCRcn,hKm,hCgap,hC,
    hη₀,hη₀1,hc,hc1,cRate,hcRate,?_⟩
  intro L μ κ Δ ε ρg σf hL hμ hκ hκeq hΔ hε hρg hacc
  obtain ⟨hB,dim,hdim,hAll,hn,hcount,hmicro,hsize,hExpected,hfamily⟩ :=
    hmain L μ κ Δ ε ρg σf hL hμ hκ hκeq hΔ hε hρg hacc
  dsimp only
  refine ⟨hB,dim,hdim,hAll,hn,hcount,hmicro,hsize,?_,hfamily⟩
  apply UpperNoiseExpectedProperty.rateProperty (H := hExpected)
  exact actual_upper_noise_query_rate hη hη₀ hL hΔ hCg hCb hε hcn hC hκ hlen hcount hsize

end Bilevel.ChiUpperNoise
