import Bilevel.ChiCanonicalHardness
import Bilevel.ChiBoundedThetaFullOracleRate

/-! Bounded-theta lower-noise hardness in the actual conservative original-SFO
model. All numerical constants are chosen before the public problem budgets. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration
open PrimitiveQuery ChiHierarchyHaar
set_option autoImplicit false
set_option maxHeartbeats 1400000

theorem bounded_theta_query_hardness (Θ : ℝ) (hΘ : 1≤Θ) :
    ∃ c cq : ℝ,0<c ∧ c≤1 ∧ 0<cq ∧
    ∀ (L μ κ θ Δ ε R₀ σf σg : ℝ),
      0<L → 0<μ → 2≤κ → κ=L/μ → 1≤θ → θ≤Θ → 0<Δ → 0<ε → 0≤R₀ →
      ε≤c*min L (Real.sqrt (L*Δ)) →
      Hardness (conservativeClass (μ:=μ) (L:=L) (ρ:=θ*μ) (Δ:=Δ) (R₀:=R₀) (σf:=σf) (σg:=σg)) ε
        (cq*(L*(1+θ)*κ^2*Δ/ε^2+ChiRefinementRates.lowerNoise L θ κ σg Δ ε)) := by
  obtain ⟨t,η,ζ,cn,CR,Km,Cgap,η₀,bStar,Cf,c,Bs,ht,ht1,hη,hη1,hζ,hζsmall,hcn,hcn1,hlen,hCR,hCRcn,hKm,hCgap,
    hη₀,hη₀1,hbs,hbs1,hbsgap,hCf,hc,hc1,hBs,cRate,hcRate,hmain⟩ := bounded_theta_full_oracle_rate_witness.{0,0} Θ hΘ
  refine ⟨c,cRate,hc,hc1,hcRate,?_⟩
  intro L μ κ θ Δ ε R₀ σf σg hL hμ hκ hκeq hθ hθΘ hΔ hε hR₀ hacc
  obtain ⟨hB,dim,hdim,hAll,hS,hn,hn₀,hrp,hratio,hcount,H,hRate,hfamily⟩ :=
    hmain L μ κ θ Δ ε σg hL hμ hκ hκeq hθ hθΘ hΔ hε hacc
  apply H.conservative_hardness μ (θ*μ) Δ R₀ σf σg _ _ hR₀ hB _ hRate
  intro a
  obtain ⟨hv,hw,hb,hi12,hvir,P,hf,hg,r,hr0,hgap,hresponse,hmean,hunique,hzero,hbarrier,hi,hsig,hO,hFull⟩ := hfamily a
  exact ⟨P,r,hr0,hgap,hmean,hFull⟩

end Bilevel.ChiExtensionCalibration
