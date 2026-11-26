import Bilevel.ChiUpperNoiseExpectedDimension
import Bilevel.ChiUpperNoisePublicWitness

/-! One fixed public dimension, the actual upper-noise Primitive/SFO family,
and the same original-SFO expected-query lower bound. No transcript,
probability-of-failure, or local-reply premise remains. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.ChiUpperNoise
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry ChiExtensionCalibration
  PartialLegendre ChiHierarchyHaar ChiHierarchyIndex ChiTreeProgress ChiCurvatureSchedule

set_option maxHeartbeats 1000000 in
theorem upper_noise_expected_witness : ∃ t η ζ cn CR Km Cgap C η₀ c : ℝ,
    0<t ∧ t<1 ∧ 0<η ∧ η≤1 ∧ 0<ζ ∧ ζ≤2/15 ∧ 0<cn ∧ cn≤1 ∧
    128≤cn/η^2 ∧ 1≤CR ∧ ζ*Real.sqrt cn≤CR ∧ 1≤Km ∧ 1≤Cgap ∧ 1≤C ∧
    0<η₀ ∧ η₀≤1 ∧ 0<c ∧ c≤1 ∧
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
      UpperNoiseExpectedProperty n dim cn (fun _ => 1) (resolution η Kg) hdim hAll sc weight ζ CR Km rad R K ε μ L
        (BernoulliOracle.probability B σf) (BernoulliOracle.probability_le_one hB) ∧
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
    hη₀,hη₀1,hc,hc1,hmain⟩ := upper_noise_public_witness
  refine ⟨t,η,ζ,cn,CR,Km,Cgap,C,η₀,c,ht,ht1,hη,hη1,hζ,hζsmall,hcn,hcn1,hlen,hCR,hCRcn,hKm,hCgap,hC,
    hη₀,hη₀1,hc,hc1,?_⟩
  intro L μ κ Δ ε ρg σf hL hμ hκ hκeq hΔ hε hρg hacc
  dsimp only
  let K := κ/6
  let Kg := max K (1/η)
  let ℓ := η₀*L
  let b := baseWidth (96/(t*η)) ε η₀ L
  let sc : Scale := ⟨ℓ,b⟩
  let n := macroIndex Δ Cgap (ℓ*b^2)
  let weight := fun j : ℕ => t^(j+1)
  let rad := sourcePublicRadialWeight sc (fun _ => 1) (resolution η Kg) weight ζ
  let R := sourcePublicNodeRadius sc (fun _ => 1) (resolution η Kg) weight CR ζ
  let B := C*(96/(t*η))*ε/K
  have hK : 0<K := by dsimp [K]; linarith only [hκ]
  have hKg : 0<Kg := hK.trans_le (le_max_left _ _)
  have hl : 0<sc.curvature := mul_pos hη₀ hL
  have hb : 0<b := by dsimp [b,baseWidth]; positivity
  have hB : 0<B := by
    have hC0 : 0<C := zero_lt_one.trans_le hC
    dsimp [B]
    positivity
  have hres (j : ℕ) : resolution η Kg j≤1 :=
    (base_resolution_le hKg (le_max_right _ _) hη j).trans hη1
  have hw (j : ℕ) : 0<weight j := pow_pos ht (j+1)
  obtain ⟨dim,hdim,hAll,hexp⟩ := exists_upper_noise_expected_dimension n sc cn η Kg μ L K ε
    (BernoulliOracle.probability B σf) CR ζ Km weight hl hb hcn.le hη hKg hres hw
    (zero_lt_one.trans_le hCR) hζ (zero_lt_one.trans_le hKm)
    (BernoulliOracle.probability_pos hB) (BernoulliOracle.probability_le_one hB) hε
  obtain ⟨hn,hcount,hmicro,hsize,hfamily⟩ := hmain L μ κ Δ ε ρg hL hμ hκ hκeq hΔ hε hρg hacc dim hdim hAll
  have hbarrier : UpperNoiseBarrier n dim cn (fun _ => 1) (resolution η Kg) hdim hAll sc weight ζ CR Km rad R K ε := by
    intro a x hx
    obtain ⟨P,_,_,_,_,r,_,_,_,hm,_,hmarg,_⟩ := hfamily a
    have hh := hmarg x hx
    rw [ChiPrimitive.mean_gradient_eq P r _ hm x] at hh
    exact hh
  exact ⟨hB,dim,hdim,hAll,hn,hcount,hmicro,hsize,hexp hbarrier,hfamily⟩

end Bilevel.ChiUpperNoise
