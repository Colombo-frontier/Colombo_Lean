import Bilevel.ChiCanonicalHardness
import Bilevel.ChiWideFullOracleRate

/-! Wide-theta lower-noise hardness for actual conservative original queries,
with no information or admissibility premise left to the calling algorithm. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration
open PrimitiveQuery ChiHierarchyHaar
set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem wide_query_hardness :
    ∃ CT c cq : ℝ,1≤CT ∧ 0<c ∧ c≤1 ∧ 0<cq ∧ ∃ q : ℕ,
    ∀ (L μ κ θ Δ ε R₀ σf σg : ℝ),
      0<L → 0<μ → 2≤κ → κ=L/μ → θ≤κ^2 → wideBranchThreshold CT≤θ →
      0<Δ → 0<ε → 0≤R₀ → ε≤c*min L (Real.sqrt (L*Δ)) →
      Hardness (conservativeClass (μ:=μ) (L:=L) (ρ:=θ*μ) (Δ:=Δ) (R₀:=R₀) (σf:=σf) (σg:=σg)) ε
        (cq*(L*(1+θ)*κ^2*Δ/ε^2+ChiRefinementRates.lowerNoise L θ κ σg Δ ε)/(Real.log (2+θ))^q) := by
  obtain ⟨t,η,ζ,cn,CR,Km,Cgap,η₀,bStar,Cf,CT,c,Bs,ht,ht1,hη,hη1,hζ,hζsmall,hcn,hcn1,hlen,hCR,hCRcn,hKm,hCgap,
    hη₀,hη₀1,hbs,hbs1,hbsgap,hCf,hCT,hc,hc1,hBs,cRate,hcRate,q,hmain⟩ :=
      wide_full_oracle_rate_witness.{0,0} 0 (by norm_num)
  refine ⟨CT,c,cRate,hCT,hc,hc1,hcRate,q,?_⟩
  intro L μ κ θ Δ ε R₀ σf σg hL hμ hκ hκeq hθκ hbranch hΔ hε hR₀ hacc
  obtain ⟨hB,dim,hdim,hAll,hJ,hS,hn,hn₀,hrp,hratio,hcount,H,hRate,hfamily⟩ :=
    hmain L μ κ θ Δ ε σg hL hμ hκ hκeq hθκ hbranch hΔ hε hacc
  apply H.conservative_hardness μ (θ*μ) Δ R₀ σf σg _ _ hR₀ hB _ hRate
  intro a
  obtain ⟨hv,hw,hforce,hb,hi12,hvir,P,hf,hg,r,hr0,hgap,hresponse,hmean,hunique,hzero,hbarrier,hi,hsig,hO,hFull⟩ := hfamily a
  exact ⟨P,r,hr0,hgap,hmean,hFull⟩

end Bilevel.ChiExtensionCalibration
