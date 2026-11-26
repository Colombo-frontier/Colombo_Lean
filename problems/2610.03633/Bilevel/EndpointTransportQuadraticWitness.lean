import Bilevel.EndpointTransportQuadraticUniformSource
import Bilevel.EndpointTransportQuadraticPrimitive
import Bilevel.ChiUpperNoiseCount

/-! Actual exact-quadratic endpoint hard family, with full accuracy window,
zero lower initialization, prescribed gap and source gradient barrier.
The original adaptive transport SFO information proof is separate. -/
noncomputable section
set_option maxHeartbeats 1800000
open Filter
open scoped Topology
namespace Bilevel.EndpointTransportResponse
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry ChiExtensionCalibration ChiUpperNoise
set_option autoImplicit false

theorem quadratic_physical_witness : ∃ t η ζ cn CR Km Cgap C η₀ c : ℝ,
    0<t ∧ t<1 ∧ 0<η ∧ η≤1 ∧ 0<ζ ∧ ζ≤2/15 ∧ 0<cn ∧ cn≤1 ∧
    128≤cn/η^2 ∧ 1≤CR ∧ ζ*Real.sqrt cn≤CR ∧ 1≤Km ∧ 1≤Cgap ∧ 1≤C ∧
    0<η₀ ∧ η₀≤1 ∧ 0<c ∧ c≤1 ∧
    ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [FiniteDimensional ℝ E] (dim : ℕ) (L κ Δ ε ρg : ℝ),
      0<L → 3200≤κ → 0<Δ → 0<ε → 0≤ρg → ε≤c*min L (Real.sqrt (L*Δ)) →
      let K := EndpointTransportNormalization.gain κ
      let Kg := max K (1/η)
      let ℓ := η₀*L
      let b := baseWidth (96/(t*η)) ε η₀ L
      let initial : Scale := ⟨ℓ,b⟩
      let n := macroIndex Δ Cgap (ℓ*b^2)
      128≤n ∧ η₀*L*Δ/(4*Cgap*(96/(t*η))^2*ε^2)≤(n:ℝ) ∧
      128≤ChiUpperNoise.microLength cn Kg ∧
      sourceChainIndex cn 1 (1/Kg)+1=ChiUpperNoise.microLength cn Kg ∧
      ∀ (Q : Rotations (EndpointTransportNormalization.interiors κ) dim)
        (U : Space n →ₗᵢ[ℝ] E)
        (V : ∀ j,List ℕ → Space (sourceChainIndex cn 1 (resolution η Kg j)) →ₗᵢ[ℝ] Block dim),
      let M : Node E := sourceMacroNode n initial Km U
      let G : Geometry (Block dim) := sourceGeometry initial (fun _ => 1) (resolution η Kg) (fun j => t^(j+1)) 3 1 ζ cn CR V
      let R := fun j => (G j []).radius
      let ρ := fun j => t^(j+1)*(G j []).nu
      ∃ P : Model.Primitive (X:=Joint E (Block dim))
        (Y:=Physical (EndpointTransportNormalization.interiors κ) dim) (L/κ) L L L ρg,
        (∀ x y,P.f x y=quadraticCore Q M (ℓ/24) G (ρ 0) (R 0) (pack x.fst y)) ∧
        (∀ x y,P.g x y=lower (L/16) (L/4) Q x.snd y) ∧
        (∀ x y,P.gyy x y=physicalHessian (L/16) Q) ∧
        ∃ r : P.Response,r.y 0=0 ∧
          (∀ x,r.y x=physicalResponse (L/16) (L/4) Q x.snd) ∧
          Nonempty (P.GapCertificate r 0 Δ) ∧
          (∀ x,P.hyperobjective r x=quadraticSourceMean M (ℓ/24) G ρ R K (oneBlockCoordinates x)) ∧
          (∀ x y,P.IsLowerSolution x y ↔ y=r.y x) ∧ P.hyperobjective r 0=0 ∧
          ∀ x,M.coordinates x.fst (Fin.last n)<b → 8*ε≤‖gradient (P.hyperobjective r) x‖ := by
  obtain ⟨t,η,ζ,cn,CR,Km,Cgap,C,η₀,c,ht,ht1,hη,hη1,hζ,hζsmall,hcn,hcn1,hlen,hCR,hCRcn,hKm,hCgap,hC,
    hη₀,hη₀1,hc,hc1,hsource⟩ := source_quadratic_uniform_certificate
  refine ⟨t,η,ζ,cn,CR,Km,Cgap,C,η₀,c,ht,ht1,hη,hη1,hζ,hζsmall,hcn,hcn1,hlen,hCR,hCRcn,hKm,hCgap,hC,
    hη₀,hη₀1,hc,hc1,?_⟩
  intro E _ _ _ _ dim L κ Δ ε ρg hL hκ hΔ hε hρg hacc
  dsimp only
  let K := EndpointTransportNormalization.gain κ
  let Kg := max K (1/η)
  let ℓ := η₀*L
  let b := baseWidth (96/(t*η)) ε η₀ L
  let initial : Scale := ⟨ℓ,b⟩
  let n := macroIndex Δ Cgap (ℓ*b^2)
  have hK : 0<K := EndpointTransportNormalization.gain_pos hκ
  have hKlow : 1/3≤K := by
    have h := (EndpointTransportNormalization.gain_bounds hκ).1
    change 1/3≤EndpointTransportNormalization.gain κ
    linarith only [h,hκ]
  have hKg : 0<Kg := hK.trans_le (le_max_left _ _)
  have hM := ChiUpperNoise.micro_length_exact
    (ChiUpperNoise.micro_length_argument hcn hη hKg hlen (le_max_right _ _))
  obtain ⟨hn,hcount,_⟩ := hsource E (EndpointTransportNormalization.interiors κ) dim L Δ ε K hL hΔ hε hKlow hacc
  refine ⟨hn,hcount,hM.2.1,hM.1,?_⟩
  intro Q U V
  let M : Node E := sourceMacroNode n initial Km U
  let G : Geometry (Block dim) := sourceGeometry initial (fun _ => 1) (resolution η Kg) (fun j => t^(j+1)) 3 1 ζ cn CR V
  let R := fun j => (G j []).radius
  let ρ := fun j => t^(j+1)*(G j []).nu
  let obj := quadraticSourceMean M (ℓ/24) G ρ R K
  obtain ⟨_hell,_hwidth,hbudgets,hcoer,hzero,hgap,hmargin⟩ :=
    (hsource E (EndpointTransportNormalization.interiors κ) dim L Δ ε K hL hΔ hε hKlow hacc).2.2 U V Q
  obtain ⟨P₀,hf,hg,hyy,r₀,hrzero,hr,hm,hu⟩ := quadratic_core_primitive_of_budgets hL hκ Q M (ℓ/24) G ρ R
    (fun z => (hbudgets z).1) (fun z => (hbudgets z).2)
  let P := ChiPrimitive.enlargeVariation P₀ ρg hρg
  let r := ChiPrimitive.enlargeVariationResponse P₀ ρg hρg r₀
  have hm' (x : Joint E (Block dim)) : P.hyperobjective r x=obj (oneBlockCoordinates x) := hm x
  have hcont : Continuous obj := (jointOuter_contDiff 1 M (ℓ/24) G ρ R 0 K 0).continuous
  obtain ⟨zmin,hmin⟩ := hcont.exists_forall_le hcoer
  have hbdd : BddBelow (Set.range obj) := ⟨obj zmin,by rintro _ ⟨z,rfl⟩;exact hmin z⟩
  have hgc := source_quadratic_gap_transfer P r obj hm' (sInf (Set.range obj)) Δ
    (fun z => csInf_le hbdd ⟨z,rfl⟩) hgap
  refine ⟨P,hf,hg,hyy,r,hrzero,hr,hgc,hm',hu,?_,?_⟩
  · rw [hm',map_zero]
    exact hzero
  · intro x hx
    rw [source_quadratic_gradient_norm M (ℓ/24) G ρ R P r hm' x]
    exact hmargin (oneBlockCoordinates x) hx

end Bilevel.EndpointTransportResponse
