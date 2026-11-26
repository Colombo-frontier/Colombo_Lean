import Bilevel.TransportQuadraticQueryFamily
import Bilevel.TransportQuadraticLowerTheorem

/-! Exact-gradient physical transport hardness in the actual conservative
curvature-constrained query model, for the large-kappa branch. -/
noncomputable section
namespace Bilevel.TransportHierarchy
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry ChiExtensionCalibration
  EndpointTransportResponse ChiUpperNoise ChiHierarchyIndex ChiTreeProgress ChiCurvatureSchedule PrimitiveQuery
set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem quadratic_high_kappa_model_hardness :
    ∃ c cq : ℝ,0<c ∧ c≤1 ∧ 0<cq ∧
    ∀ (L κ ρ Δ ε R₀ σf σg : ℝ),
      0<L → 3200≤κ → 0≤ρ → 0<Δ → 0<ε → 0≤R₀ →
      ε≤c*min L (Real.sqrt (L*Δ)) →
      Hardness (conservativeCurvatureClass (μ:=L/κ) (L:=L) (ρ:=ρ) (Δ:=Δ)
        (R₀:=R₀) (σf:=σf) (σg:=σg) (4*L*κ^2)) ε
        (cq*(L*κ^2*Real.sqrt κ*Δ/ε^2)) := by
  classical
  obtain ⟨t,η,ζ,cn,CR,Km,Cgap,C,η₀,c,ht,ht1,hη,hη1,hζ,hζsmall,hcn,hcn1,hlen,hCR,hCRcn,hKm,hCgap,hC,
    hη₀,hη₀1,hc,hc1,cRate,hcRate,hmain⟩ := quadratic_transport_lower
  refine ⟨c,cRate,hc,hc1,hcRate,?_⟩
  intro L κ ρ Δ ε R₀ σf σg hL hκ hρ hΔ hε hR₀ hacc
  obtain ⟨dim,hdim,hAll,hT,hn,hcount,hmicro,hsize,hRate,hfamily⟩ :=
    hmain L κ Δ ε ρ hL hκ hΔ hε hρ hacc
  let layers := EndpointTransportNormalization.interiors κ
  let K := EndpointTransportNormalization.gain κ
  let Kg := max K (1/η)
  let b := baseWidth (96/(t*η)) ε η₀ L
  let sc : Scale := ⟨η₀*L,b⟩
  let n := macroIndex Δ Cgap ((η₀*L)*b^2)
  let w := fun j : ℕ => t^(j+1)
  let rad := sourcePublicRadialWeight sc (fun _ => 1) (resolution η Kg) w ζ
  let R := sourcePublicNodeRadius sc (fun _ => 1) (resolution η Kg) w CR ζ
  have hP : ∀ a : PhysicalSample (sourceCounts n cn (fun _ => 1) (resolution η Kg)) 0 layers dim,
      ∃ P : Model.Primitive (X:=QuadraticOutput dim) (Y:=Physical layers dim) (L/κ) L L L ρ,
      ∃ r : P.Response,r.y 0=0 ∧ Nonempty (P.GapCertificate r 0 Δ) ∧
        (∀ x,P.hyperobjective r x=jointOuter 1
          (sourcePhysicalMacro n 0 layers dim cn (fun _ => 1) (resolution η Kg) hAll a sc Km) (sc.curvature/24)
          (sourcePhysicalGeometry n 0 layers dim cn (fun _ => 1) (resolution η Kg) hdim hT a sc w 3 1 ζ CR)
          rad R 0 K (oneBlockCoordinates x)) ∧
        (∀ x x',‖gradient (P.hyperobjective r) x-gradient (P.hyperobjective r) x'‖≤(4*L*κ^2)*‖x-x'‖) ∧
        HasQuadraticFullOracle n layers dim cn (fun _ => 1) (resolution η Kg) hdim hAll hT sc w ζ CR Km rad R
          (L/κ) L ρ (L/16) (L/4) a P := by
    intro a
    obtain ⟨P,hf,hg,hyy,r,hr0,hr,hgap,hm,hu,hzero,hbarrier,hFull,hcurv⟩ := hfamily a
    refine ⟨P,r,hr0,hgap,hm,?_,hFull⟩
    intro x x'
    simpa only [dist_eq_norm] using hcurv.dist_le_mul x x'
  choose P r hz hgap hm hcurv hfull using hP
  obtain ⟨hD,F,hF,hcons,hmean⟩ := quadratic_query_family n layers dim cn (fun _ => 1) (resolution η Kg)
    hdim hAll hT sc w ζ CR Km rad R K ε (L/κ) L ρ Δ R₀ σf σg (L/16) (L/4)
    (cRate*L*κ^2*Real.sqrt κ*Δ/ε^2) hR₀ P r hgap hz hm hfull hRate
  have hHard := F.hardness (conservativeCurvatureClass (4*L*κ^2)) ε _ (fun a => by
    refine ⟨hcons a,?_⟩
    intro x x'
    change ‖gradient ((F.primitive a).hyperobjective (F.response a)) x-
      gradient ((F.primitive a).hyperobjective (F.response a)) x'‖≤(4*L*κ^2)*‖x-x'‖
    rw [funext (hmean a)]
    exact hcurv a x x') hF
  apply hHard.mono
  exact le_of_eq (by ring)

end Bilevel.TransportHierarchy
