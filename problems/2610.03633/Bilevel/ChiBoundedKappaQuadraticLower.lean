import Bilevel.ChiUpperNoiseLowerTheorem
import Bilevel.ChiUpperNoiseExactOracle
import Bilevel.ChiUpperNoiseNoiselessRate

/-! The bounded-kappa exact-quadratic branch. The original upper-noise
family is specialized at zero variance; its actual seed law is a point mass.
The same SFO, mean objective, and arbitrary-output expected-query property
therefore give the deterministic transport rate, paying sqrt(3200). -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.ChiUpperNoise
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry ChiExtensionCalibration
  PartialLegendre ChiHierarchyHaar ChiHierarchyIndex ChiTreeProgress ChiCurvatureSchedule

set_option maxHeartbeats 1000000 in
theorem bounded_kappa_quadratic_lower : ∃ t η ζ cn CR Km Cgap C η₀ c : ℝ,
    0<t ∧ t<1 ∧ 0<η ∧ η≤1 ∧ 0<ζ ∧ ζ≤2/15 ∧ 0<cn ∧ cn≤1 ∧
    128≤cn/η^2 ∧ 1≤CR ∧ ζ*Real.sqrt cn≤CR ∧ 1≤Km ∧ 1≤Cgap ∧ 1≤C ∧
    0<η₀ ∧ η₀≤1 ∧ 0<c ∧ c≤1 ∧
    ∃ cRate : ℝ,0<cRate ∧
    ∀ (L μ κ Δ ε ρg : ℝ),0<L → 0<μ → 2≤κ → κ≤3200 → κ=L/μ → 0<Δ → 0<ε → 0≤ρg →
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
        (BernoulliOracle.probability B 0) (BernoulliOracle.probability_le_one hB)
        (cRate*L*κ^2*Real.sqrt κ*Δ/ε^2) ∧
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
            (publicLower μ L) (C*(96/(t*η))*ε/K) ∧
          HasUpperNoiseFullOracle n dim cn (fun _ => 1) (resolution η Kg) hdim hAll sc weight ζ CR Km rad R μ L ρg B a P ∧
          NoiselessUpperNoiseOriginal n dim cn (fun _ => 1) (resolution η Kg) hdim hAll sc weight ζ CR Km rad R μ L ρg B hB a P ∧
          LipschitzWith ⟨L*κ^2,mul_nonneg P.Lf_nonneg (sq_nonneg _)⟩ (gradient (P.hyperobjective r)) ∧
          ∀ x y,P.IsLowerSolution x y ↔ y=r.y x := by
  obtain ⟨t,η,ζ,cn,CR,Km,Cgap,C,η₀,c,ht,ht1,hη,hη1,hζ,hζsmall,hcn,hcn1,hlen,hCR,hCRcn,hKm,hCgap,hC,
    hη₀,hη₀1,hc,hc1,cRate,hcRate,hmain⟩ := upper_noise_lower
  refine ⟨t,η,ζ,cn,CR,Km,Cgap,C,η₀,c,ht,ht1,hη,hη1,hζ,hζsmall,hcn,hcn1,hlen,hCR,hCRcn,hKm,hCgap,hC,
    hη₀,hη₀1,hc,hc1,cRate/Real.sqrt 3200,by positivity,?_⟩
  intro L μ κ Δ ε ρg hL hμ hκ hκmax hκeq hΔ hε hρg hacc
  dsimp only
  obtain ⟨hB,dim,hdim,hAll,hn,hcount,hmicro,hsize,hRate,hfamily⟩ :=
    hmain L μ κ Δ ε ρg 0 hL hμ hκ hκeq hΔ hε hρg hacc
  refine ⟨hB,dim,hdim,hAll,hn,hcount,hmicro,hsize,?_,?_⟩
  · apply upperNoiseRateProperty_mono (H := hRate)
    simpa only [zero_pow (by norm_num : 2≠0),mul_zero,zero_mul,zero_div,add_zero] using
      bounded_kappa_noiseless_rate (ε:=ε) hcRate.le hL.le hΔ.le hκmax
  · intro a
    obtain ⟨P,hf,hg,hgy,hyy,r,hr,hr0,hgap,hm,hzero,hbarrier,hO,hFull,hLip,hu⟩ := hfamily a
    refine ⟨P,hf,hg,hgy,hyy,r,hr,hr0,hgap,hm,hzero,hbarrier,hO,hFull,?_,hLip,hu⟩
    apply HasUpperNoiseFullOracle.noiseless
    exact hFull

end Bilevel.ChiUpperNoise
