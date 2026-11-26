import Bilevel.MultiscaleBoundedGapExpected
import Bilevel.MultiscaleInnerCertifiedOracles
import Bilevel.ChiCertifiedOracleProperty
import Bilevel.ChiExpectedRateProperty

/-! Compact retained hard families for the all-gap curvature class.
Both alternatives contain actual original-SFO execution theorems and the
same Primitive's response, gap and full-oracle certificate. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Bilevel.ChiCurvatureLower
open PrimitiveGeometry ChiBoundedChain ChiRecursive ChiCarrier ChiOuter ChiExtension
  ChiExtensionCalibration ChiHierarchyHaar ChiHierarchyIndex ChiTreeProgress MultiscaleMean
universe u v

def InnerFamily (μ L ρ Δ C κ ε σ cost : ℝ) : Prop :=
  ∃ n dim : ℕ,∃ P : MultiscaleMean.Parameters (E:=EuclideanGaussian.Space dim) n,
  ∃ hD : ∀ i : FrameIndex (SingleFrameSource.counts n) 0,chainSize i+1≤dim,
    P.β*P.θ≤1 ∧
    InnerRateProperty.{u,v} P hD (P.activationProbability σ) (P.activationProbability_le_one σ) ε cost ∧
    ∀ a,InnerPrimitiveCertificate (P.withFrame (frame hD a (Sum.inl ()))) μ L ρ Δ C κ ε

def CanonicalFamily (μ L ρ Δ C κ ε σ cost : ℝ) : Prop :=
  ∃ n dim : ℕ,∃ cn : ℝ,∃ ratios resolutions : ℕ → ℝ,
  ∃ hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤dim,
  ∃ hAll : ∀ i : FrameIndex (sourceCounts n cn ratios resolutions) 1,chainSize i+1≤dim,
  ∃ sc : Scale,∃ weight : ℕ → ℝ,∃ ζ CR Km v : ℝ,∃ rad R : ℕ → ℝ,∃ K B : ℝ,
  ∃ hB : 0<B,
  ∃ H : CanonicalQueryCertificate n 1 dim cn ratios resolutions hdim hAll sc weight ζ CR Km
      (by norm_num) v rad R L K ε,
    CanonicalQueryCertificate.RateProperty.{u,v} H μ (BernoulliOracle.probability B σ) (BernoulliOracle.probability_le_one hB) cost ∧
    ∀ a : Orientations (sourceCounts n cn ratios resolutions) 1 dim,
    ∃ P : Model.Primitive
      (X:=Joint (EuclideanGaussian.Space dim) (Blocks 2 (EuclideanGaussian.Space dim)))
      (Y:=Joint (Blocks 2 (EuclideanGaussian.Space dim)) (Normals 2)) μ L L L ρ,
    ∃ r : P.Response,r.y 0=0 ∧ Nonempty (P.GapCertificate r 0 Δ) ∧
      (∀ x,P.hyperobjective r x=jointOuter 2
        (sourceCanonicalMacro n 1 dim cn ratios resolutions hAll a sc Km) (sc.curvature/24)
        (sourceCanonicalGeometry n 1 dim cn ratios resolutions hdim a sc weight 3 1 ζ CR) rad R 1 K x) ∧
      (∀ x z,‖gradient (P.hyperobjective r) x-gradient (P.hyperobjective r) z‖≤(C*L*κ^2)*‖x-z‖) ∧
      H.HasFullOracle μ ρ B a P

/-- The alternatives use two measurably equivalent presentations of the full
query channel; neither alternative is an assumed information lemma. -/
def Family (μ L ρ Δ C κ ε σ cost : ℝ) : Prop :=
  InnerFamily.{u,v} μ L ρ Δ C κ ε σ cost ∨ CanonicalFamily.{u,v} μ L ρ Δ C κ ε σ cost

theorem innerFamily_mono {μ L ρ Δ C C' κ ε σ cost cost' : ℝ}
    (hL : 0≤L) (hC : C≤C') (hc : cost'≤cost)
    (H : InnerFamily.{u,v} μ L ρ Δ C κ ε σ cost) :
    InnerFamily.{u,v} μ L ρ Δ C' κ ε σ cost' := by
  obtain ⟨n,dim,P,hD,hs,hR,hP⟩ := H
  refine ⟨n,dim,P,hD,hs,@innerRateProperty_mono.{u,v} n dim P hD _ _ ε _ _ hR hc,?_⟩
  intro a
  obtain ⟨Q,r,hf,hg,hr,hm,hz,hgap,hcoerc,hcurv,hblind⟩ := hP a
  refine ⟨Q,r,hf,hg,hr,hm,hz,hgap,hcoerc,?_,hblind⟩
  intro x z
  apply (hcurv x z).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hL) (sq_nonneg κ)) (norm_nonneg _)

theorem canonicalFamily_mono {μ L ρ Δ C C' κ ε σ cost cost' : ℝ}
    (hL : 0≤L) (hC : C≤C') (hc : cost'≤cost)
    (H : CanonicalFamily.{u,v} μ L ρ Δ C κ ε σ cost) :
    CanonicalFamily.{u,v} μ L ρ Δ C' κ ε σ cost' := by
  obtain ⟨n,dim,cn,rat,res,hd,hAll,sc,w,ζ,CR,Km,v,rad,R,K,B,hB,H,hR,hP⟩ := H
  refine ⟨n,dim,cn,rat,res,hd,hAll,sc,w,ζ,CR,Km,v,rad,R,K,B,hB,H,?_,?_⟩
  · intro instMX instBX instMY instBY instMR instBR instMQ instBQ Private State instP instS alg initial hi law instLaw hacc
    obtain ⟨a,ha⟩ := @hR instMX instBX instMY instBY instMR instBR instMQ instBQ
      Private State instP instS alg initial hi law instLaw hacc
    exact ⟨a,(ENNReal.ofReal_le_ofReal hc).trans ha⟩
  · intro a
    obtain ⟨P,r,hz,hgap,hm,hcurv,hO⟩ := hP a
    refine ⟨P,r,hz,hgap,hm,?_,hO⟩
    intro x z
    apply (hcurv x z).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hL) (sq_nonneg κ)) (norm_nonneg _)

theorem family_mono {μ L ρ Δ C C' κ ε σ cost cost' : ℝ}
    (hL : 0≤L) (hC : C≤C') (hc : cost'≤cost)
    (H : Family.{u,v} μ L ρ Δ C κ ε σ cost) :
    Family.{u,v} μ L ρ Δ C' κ ε σ cost' :=
  H.elim (fun h => Or.inl (innerFamily_mono hL hC hc h))
    (fun h => Or.inr (canonicalFamily_mono hL hC hc h))

end Bilevel.ChiCurvatureLower
