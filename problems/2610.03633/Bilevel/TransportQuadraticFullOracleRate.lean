import Bilevel.TransportQuadraticExpectedRate
import Bilevel.TransportQuadraticOracleProperty

/-! Actual deterministic endpoint-transport rate with the full original
conservative SFO pair for the very same Primitive, gap and mean objective. -/
noncomputable section
namespace Bilevel.TransportHierarchy
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry ChiExtensionCalibration
  EndpointTransportResponse ChiUpperNoise ChiHierarchyIndex ChiTreeProgress
set_option autoImplicit false
set_option maxHeartbeats 1500000

theorem quadratic_full_oracle_rate_witness : ∃ t η ζ cn CR Km Cgap C η₀ c : ℝ,
    0<t ∧ t<1 ∧ 0<η ∧ η≤1 ∧ 0<ζ ∧ ζ≤2/15 ∧ 0<cn ∧ cn≤1 ∧
    128≤cn/η^2 ∧ 1≤CR ∧ ζ*Real.sqrt cn≤CR ∧ 1≤Km ∧ 1≤Cgap ∧ 1≤C ∧
    0<η₀ ∧ η₀≤1 ∧ 0<c ∧ c≤1 ∧
    ∃ cRate : ℝ,0<cRate ∧
    ∀ (L κ Δ ε ρg : ℝ),0<L → 3200≤κ → 0<Δ → 0<ε → 0≤ρg →
      ε≤c*min L (Real.sqrt (L*Δ)) →
      let layers := EndpointTransportNormalization.interiors κ
      let K := EndpointTransportNormalization.gain κ
      let Kg := max K (1/η)
      let ℓ := η₀*L
      let b := baseWidth (96/(t*η)) ε η₀ L
      let sc : Scale := ⟨ℓ,b⟩
      let macroN := macroIndex Δ Cgap (ℓ*b^2)
      let weight := fun j => t^(j+1)
      let rad := sourcePublicRadialWeight sc (fun _ => 1) (resolution η Kg) weight ζ
      let R := sourcePublicNodeRadius sc (fun _ => 1) (resolution η Kg) weight CR ζ
      ∃ (dim : ℕ),
      ∃ (hdim : ∀ j,sourceChainIndex cn 1 (resolution η Kg j)+1≤dim),
      ∃ (hAll : ∀ i : FrameIndex (sourceCounts macroN cn (fun _ => 1) (resolution η Kg)) 0,chainSize i+1≤dim),
      ∃ (hT : capacity (sourceCounts macroN cn (fun _ => 1) (resolution η Kg)) 1 0≤dim),
      128≤macroN ∧ η₀*L*Δ/(4*Cgap*(96/(t*η))^2*ε^2)≤(macroN:ℝ) ∧
      128≤microLength cn Kg ∧ sourceChainIndex cn 1 (1/Kg)+1=microLength cn Kg ∧
      QuadraticRateProperty macroN layers dim cn (fun _ => 1) (resolution η Kg) hdim hAll hT
        sc weight ζ CR Km rad R K ε (L/16) (L/4) (cRate*L*κ^2*Real.sqrt κ*Δ/ε^2) ∧
      ∀ a : PhysicalSample (sourceCounts macroN cn (fun _ => 1) (resolution η Kg)) 0 layers dim,
      let Q := physicalRotations a.1
      let M := sourcePhysicalMacro macroN 0 layers dim cn (fun _ => 1) (resolution η Kg) hAll a sc Km
      let G := sourcePhysicalGeometry macroN 0 layers dim cn (fun _ => 1) (resolution η Kg) hdim hT a sc weight 3 1 ζ CR
      ∃ P : Model.Primitive (X:=Joint (Block dim) (Block dim)) (Y:=Physical layers dim) (L/κ) L L L ρg,
        (∀ x y,P.f x y=quadraticCore Q M (ℓ/24) G (rad 0) (R 0) (pack x.fst y)) ∧
        (∀ x y,P.g x y=lower (L/16) (L/4) Q x.snd y) ∧
        (∀ x y,P.gyy x y=physicalHessian (L/16) Q) ∧
        ∃ r : P.Response,r.y 0=0 ∧
          (∀ x,r.y x=physicalResponse (L/16) (L/4) Q x.snd) ∧
          Nonempty (P.GapCertificate r 0 Δ) ∧
          (∀ x,P.hyperobjective r x=jointOuter 1 M (ℓ/24) G rad R 0 K (oneBlockCoordinates x)) ∧
          (∀ x y,P.IsLowerSolution x y ↔ y=r.y x) ∧ P.hyperobjective r 0=0 ∧
          (∀ x,M.coordinates x.fst (Fin.last macroN)<b → 8*ε≤‖gradient (P.hyperobjective r) x‖) ∧
          HasQuadraticFullOracle macroN layers dim cn (fun _ => 1) (resolution η Kg) hdim hAll hT
            sc weight ζ CR Km rad R (L/κ) L ρg (L/16) (L/4) a P := by
  obtain ⟨t,η,ζ,cn,CR,Km,Cgap,C,η₀,c,ht,ht1,hη,hη1,hζ,hζsmall,hcn,hcn1,hlen,hCR,hCRcn,hKm,hCgap,hC,
    hη₀,hη₀1,hc,hc1,cRate,hcRate,hmain⟩ := quadratic_expected_rate_witness
  refine ⟨t,η,ζ,cn,CR,Km,Cgap,C,η₀,c,ht,ht1,hη,hη1,hζ,hζsmall,hcn,hcn1,hlen,hCR,hCRcn,hKm,hCgap,hC,
    hη₀,hη₀1,hc,hc1,cRate,hcRate,?_⟩
  intro L κ Δ ε ρg hL hκ hΔ hε hρg hacc
  dsimp only
  obtain ⟨dim,hdim,hAll,hT,hn,hcount,hmicro,hsize,hRate,hfamily⟩ := hmain L κ Δ ε ρg hL hκ hΔ hε hρg hacc
  refine ⟨dim,hdim,hAll,hT,hn,hcount,hmicro,hsize,hRate,?_⟩
  intro a
  obtain ⟨P,hf,hg,hyy,r,hr0,hr,hgap,hm,hu,hzero,hbarrier⟩ := hfamily a
  refine ⟨P,hf,hg,hyy,r,hr0,hr,hgap,hm,hu,hzero,hbarrier,?_⟩
  exact hasQuadraticFullOracle _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (L/κ) L ρg (L/16) (L/4) a P hf hg

end Bilevel.TransportHierarchy
