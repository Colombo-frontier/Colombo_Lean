import Bilevel.ChiUpperNoiseQueryFamily
import Bilevel.ChiBoundedKappaQuadraticLower
import Bilevel.PrimitiveQueryNoiseMonotonicity
import Bilevel.PrimitiveQueryCurvatureMonotonicity

/-! The bounded-kappa exact-quadratic deterministic family in the common
original-query model. Zero-noise laws are preserved when enlarging the
public noise budgets; no resampling or new information argument occurs. -/
noncomputable section
namespace Bilevel.ChiUpperNoise
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry ChiExtensionCalibration
  PartialLegendre ChiHierarchyHaar ChiHierarchyIndex ChiTreeProgress ChiCurvatureSchedule PrimitiveQuery
set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem bounded_kappa_quadratic_model_hardness :
    ∃ c cq : ℝ,0<c ∧ c≤1 ∧ 0<cq ∧
    ∀ (L μ κ ρ Δ ε R₀ σf σg : ℝ),
      0<L → 0<μ → 2≤κ → κ≤3200 → κ=L/μ → 0≤ρ → 0<Δ → 0<ε → 0≤R₀ →
      ε≤c*min L (Real.sqrt (L*Δ)) →
      Hardness (conservativeCurvatureClass (μ:=μ) (L:=L) (ρ:=ρ) (Δ:=Δ)
        (R₀:=R₀) (σf:=σf) (σg:=σg) (4*L*κ^2)) ε
        (cq*L*κ^2*Real.sqrt κ*Δ/ε^2) := by
  classical
  obtain ⟨t,η,ζ,cn,CR,Km,Cgap,C,η₀,c,ht,ht1,hη,hη1,hζ,hζsmall,hcn,hcn1,hlen,hCR,hCRcn,hKm,hCgap,hC,
    hη₀,hη₀1,hc,hc1,cRate,hcRate,hmain⟩ := bounded_kappa_quadratic_lower.{0,0}
  refine ⟨c,cRate,hc,hc1,hcRate,?_⟩
  intro L μ κ ρ Δ ε R₀ σf σg hL hμ hκ hκmax hκeq hρ hΔ hε hR₀ hacc
  obtain ⟨hB,dim,hdim,hAll,hn,hcount,hmicro,hsize,hRate,hfamily⟩ :=
    hmain L μ κ Δ ε ρ hL hμ hκ hκmax hκeq hΔ hε hρ hacc
  let Kg := max (κ/6) (1/η)
  let b := baseWidth (96/(t*η)) ε η₀ L
  let sc : Scale := ⟨η₀*L,b⟩
  let n := macroIndex Δ Cgap ((η₀*L)*b^2)
  let w := fun j : ℕ => t^(j+1)
  let rad := sourcePublicRadialWeight sc (fun _ => 1) (resolution η Kg) w ζ
  let R := sourcePublicNodeRadius sc (fun _ => 1) (resolution η Kg) w CR ζ
  let B := C*(96/(t*η))*ε/(κ/6)
  have hP : ∀ a : Orientations (sourceCounts n cn (fun _ => 1) (resolution η Kg)) 0 dim,
      ∃ P : Model.Primitive (X:=UpperNoiseOutput dim) (Y:=Blocks 1 (EuclideanGaussian.Space dim)) μ L L L ρ,
      ∃ r : P.Response,r.y 0=0 ∧ Nonempty (P.GapCertificate r 0 Δ) ∧
        (∀ x,P.hyperobjective r x=jointOuter 1
          (sourceCanonicalMacro n 0 dim cn (fun _ => 1) (resolution η Kg) hAll a sc Km) (sc.curvature/24)
          (sourceCanonicalGeometry n 0 dim cn (fun _ => 1) (resolution η Kg) hdim a sc w 3 1 ζ CR) rad R 0 (κ/6) x) ∧
        (∀ x x',‖gradient (P.hyperobjective r) x-gradient (P.hyperobjective r) x'‖≤(L*κ^2)*‖x-x'‖) ∧
        HasUpperNoiseFullOracle n dim cn (fun _ => 1) (resolution η Kg) hdim hAll sc w ζ CR Km rad R μ L ρ B a P := by
    intro a
    obtain ⟨P,hf,hg,hgy,hyy,r,hr,hr0,hgap,hm,hzero,hbarrier,hO,hFull,hNoiseless,hcurv,hunique⟩ := hfamily a
    refine ⟨P,r,hr0,hgap,hm,?_,hFull⟩
    intro x x'
    simpa only [dist_eq_norm] using hcurv.dist_le_mul x x'
  choose P r hz hgap hm hcurv hfull using hP
  obtain ⟨hD,F,hF,hcons,hmean⟩ := upper_noise_query_family n dim cn (fun _ => 1) (resolution η Kg) hdim hAll sc w ζ CR Km rad R (κ/6) ε
    μ L ρ Δ R₀ 0 0 B (cRate*L*κ^2*Real.sqrt κ*Δ/ε^2) hR₀ hB P r hgap hz hm hfull hRate
  have hHard := F.hardness (conservativeCurvatureClass (L*κ^2)) ε _ (fun a => by
    refine ⟨hcons a,?_⟩
    intro x x'
    change ‖gradient ((F.primitive a).hyperobjective (F.response a)) x-
      gradient ((F.primitive a).hyperobjective (F.response a)) x'‖≤(L*κ^2)*‖x-x'‖
    rw [funext (hmean a)]
    exact hcurv a x x') hF
  have hnoise : Hardness (conservativeCurvatureClass (μ:=μ) (L:=L) (ρ:=ρ) (Δ:=Δ)
      (R₀:=R₀) (σf:=σf) (σg:=σg) (L*κ^2)) ε
      (cRate*L*κ^2*Real.sqrt κ*Δ/ε^2) :=
    hHard.enlargeNoise_conservativeCurvature (by simpa using (sq_nonneg σf)) (by simpa using (sq_nonneg σg))
  apply hnoise.enlargeConservativeCurvature
  have hn : 0≤L*κ^2 := mul_nonneg hL.le (sq_nonneg κ)
  nlinarith only [hn]

end Bilevel.ChiUpperNoise
