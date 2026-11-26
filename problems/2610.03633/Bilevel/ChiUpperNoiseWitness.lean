import Bilevel.ChiUpperNoiseUniformSource
import Bilevel.ChiUpperNoisePrimitiveOracle
import Bilevel.ChiUpperNoiseCount
import Bilevel.ChiPrimitiveObjective

/-! Actual full-window upper-noise witness for every conditioning level.
This packages the prescribed Primitive, exact public lower oracle, fixed
conservative upper oracle, attained response, gap and blind-frontier margin.
Random-frame and information/query lower bounds remain separate. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.ChiUpperNoise
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry ChiExtensionCalibration PartialLegendre
universe u

def publicLower {E U : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    (μ L : ℝ) : Queries E U → ℝ :=
  ChiQuadratic.lower ((3*μ/2) • ContinuousLinearMap.id ℝ U) ((L/4) • jointSndLinear)

theorem publicLower_formula {E U : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    (μ L : ℝ) (q : Queries E U) :
    publicLower μ L q=(3*μ/4)*‖q.snd‖^2-(L/4)*⟪q.fst.snd,q.snd⟫ := by
  change (1/2)*⟪q.snd,(3*μ/2) • q.snd⟫-⟪(L/4) • q.fst.snd,q.snd⟫=_
  rw [real_inner_smul_right,real_inner_smul_left,real_inner_self_eq_norm_sq]
  ring

set_option maxHeartbeats 1800000 in
theorem upper_noise_witness : ∃ t η ζ cn CR Km Cgap C η₀ c : ℝ,
    0<t ∧ t<1 ∧ 0<η ∧ η≤1 ∧ 0<ζ ∧ ζ≤2/15 ∧ 0<cn ∧ cn≤1 ∧
    128≤cn/η^2 ∧ 1≤CR ∧ ζ*Real.sqrt cn≤CR ∧ 1≤Km ∧ 1≤Cgap ∧ 1≤C ∧
    0<η₀ ∧ η₀≤1 ∧ 0<c ∧ c≤1 ∧
    ∀ (E F : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      [FiniteDimensional ℝ F] (L μ κ Δ ε ρg : ℝ),0<L → 0<μ → 2≤κ → κ=L/μ → 0<Δ → 0<ε → 0≤ρg →
      ε≤c*min L (Real.sqrt (L*Δ)) →
      let K := κ/6
      let Kg := max K (1/η)
      let ℓ := η₀*L
      let b := baseWidth (96/(t*η)) ε η₀ L
      let initial : Scale := ⟨ℓ,b⟩
      let n := macroIndex Δ Cgap (ℓ*b^2)
      128≤n ∧ η₀*L*Δ/(4*Cgap*(96/(t*η))^2*ε^2)≤(n:ℝ) ∧
      128≤microLength cn Kg ∧ sourceChainIndex cn 1 (1/Kg)+1=microLength cn Kg ∧
      ∀ (U : Space n →ₗᵢ[ℝ] E)
        (V : ∀ j,List ℕ → Space (sourceChainIndex cn 1 (resolution η Kg j)) →ₗᵢ[ℝ] F),
      let M := sourceMacroNode n initial Km U
      let D := sourceGeometry initial (fun _ => 1) (resolution η Kg) (fun j => t^(j+1)) 3 1 ζ cn CR V
      let R := fun j => (D j []).radius
      let ρ := fun j => t^(j+1)*(D j []).nu
      ∃ P : Model.Primitive (X:=Joint E (Blocks 1 F)) (Y:=Blocks 1 F) μ L L L ρg,
        (∀ x u,P.f x u=core 1 M (ℓ/24) D ρ R (pack x.fst u)) ∧
        (∀ x u,P.g x u=(3*μ/4)*‖u‖^2-(L/4)*⟪x.snd,u⟫) ∧
        (∀ x u,P.gy x u=(3*μ/2) • u-(L/4) • x.snd) ∧
        (∀ x u,P.gyy x u=(3*μ/2) • ContinuousLinearMap.id ℝ (Blocks 1 F)) ∧
        ∃ r : P.Response,(∀ x,r.y x=K • x.snd) ∧ r.y 0=0 ∧
          Nonempty (P.GapCertificate r 0 Δ) ∧
          (∀ x,P.hyperobjective r x=jointOuter 1 M (ℓ/24) D ρ R 0 K x) ∧
          P.hyperobjective r 0=0 ∧
          (∀ z,M.coordinates z.fst (Fin.last n)<b → 8*ε≤‖gradient (P.hyperobjective r) z‖) ∧
          HasUpperNoiseOracle P (fullCore 1 M (ℓ/24) D ρ R) (fullInactiveCore 1 M (ℓ/24) D ρ R)
            (publicLower μ L) (C*(96/(t*η))*ε/K) := by
  obtain ⟨t,η,ζ,cn,CR,Km,Cgap,C,η₀,c,ht,ht1,hη,hη1,hζ,hζsmall,hcn,hcn1,hlen,hCR,hCRcn,hKm,hCgap,hC,
    hη₀,hη₀1,hc,hc1,hsource⟩ := source_uniform_upper_certificate.{u}
  refine ⟨t,η,ζ,cn,CR,Km,Cgap,C,η₀,c,ht,ht1,hη,hη1,hζ,hζsmall,hcn,hcn1,hlen,hCR,hCRcn,hKm,hCgap,hC,
    hη₀,hη₀1,hc,hc1,?_⟩
  intro E F _ _ _ _ _ _ _ _ L μ κ Δ ε ρg hL hμ hκ hκeq hΔ hε hρg hacc
  dsimp only
  let K := κ/6
  let Kg := max K (1/η)
  let ℓ := η₀*L
  let b := baseWidth (96/(t*η)) ε η₀ L
  let initial : Scale := ⟨ℓ,b⟩
  let n := macroIndex Δ Cgap (ℓ*b^2)
  have hK : 0<K := by dsimp [K]; linarith only [hκ]
  have hKlow : 1/3≤K := by dsimp [K]; linarith only [hκ]
  have hKg : 0<Kg := hK.trans_le (le_max_left _ _)
  have hcond : 2*μ≤L := by
    have hh : 2≤L/μ := hκeq ▸ hκ
    exact (le_div_iff₀ hμ).mp hh
  have hKeq : L/(6*μ)=K := by dsimp [K]; rw [hκeq]; ring
  obtain ⟨hn,hcount,hgeometry⟩ := hsource E F L Δ ε K hL hΔ hε hKlow hacc
  have hM := micro_length_exact (micro_length_argument hcn hη hKg hlen (le_max_right _ _))
  refine ⟨hn,hcount,hM.2.1,hM.1,?_⟩
  intro U V
  let M := sourceMacroNode n initial Km U
  let D := sourceGeometry initial (fun _ => 1) (resolution η Kg) (fun j => t^(j+1)) 3 1 ζ cn CR V
  let R := fun j => (D j []).radius
  let ρ := fun j => t^(j+1)*(D j []).nu
  obtain ⟨_hell,_hwidth,hbudgets,hcoer,hzero,hgap,hmargin⟩ := hgeometry U V
  obtain ⟨P₀,hf,hg,hgy,hyy,r₀,hr₀,hm₀,_hu⟩ := direct_quadratic_primitive 1 M (ℓ/24) D ρ R hμ hcond
    (fun z => (hbudgets z).1) (fun x u => (hbudgets (pack x u)).2.1)
  let P := ChiPrimitive.enlargeVariation P₀ ρg hρg
  let r := ChiPrimitive.enlargeVariationResponse P₀ ρg hρg r₀
  have hr (x : Joint E (Blocks 1 F)) : r.y x=K • x.snd := by
    change r₀.y x=K • x.snd
    rw [hr₀,hKeq]
  have hm (x : Joint E (Blocks 1 F)) : P.hyperobjective r x=jointOuter 1 M (ℓ/24) D ρ R 0 K x := by
    change P₀.hyperobjective r₀ x=_
    rw [hm₀,hKeq]
  have hgc := ChiPrimitive.gapCertificate_of_coercive_mean P r _
    (jointOuter_contDiff 1 M (ℓ/24) D ρ R 0 K 3).continuous hcoer hm 0 Δ hgap
  refine ⟨P,hf,hg,hgy,hyy,r,hr,?_,hgc,hm,(hm 0).trans hzero,?_,?_⟩
  · rw [hr]
    change K • (0 : Blocks 1 F)=0
    exact smul_zero K
  · intro z hz
    rw [ChiPrimitive.mean_gradient_eq P r _ hm]
    exact hmargin z hz
  · have hCp : 0<C := by linarith only [hC]
    have hB : 0<C*(96/(t*η))*ε/K := by positivity
    apply direct_hasUpperNoiseOracle 1 M (ℓ/24) D ρ R hB (fun z => (hbudgets z).2.2) P hf
      (publicLower μ L) (ChiQuadratic.lower_contDiff _ _ 3)
    intro x u
    rw [publicLower_formula]
    exact hg x u

end Bilevel.ChiUpperNoise
