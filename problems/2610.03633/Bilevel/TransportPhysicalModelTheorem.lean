import Bilevel.TransportPhysicalHardness
import Bilevel.TransportPhysicalFullOracleRate

/-! Positive-depth deterministic transport hardness in the common original
query model, retaining the actual conservative same-family SFO pair. -/
noncomputable section
namespace Bilevel.TransportHierarchy
open PrimitiveQuery ChiExtensionCalibration
set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem physical_wide_model_hardness :
    ∃ CT c cq : ℝ,1≤CT ∧ 0<c ∧ c≤1 ∧ 0<cq ∧ ∃ q : ℕ,
    ∀ (L κ θ Δ ε R₀ σf σg : ℝ),
      0<L → 3200≤κ → θ≤κ^2 → wideBranchThreshold CT≤θ →
      0<Δ → 0<ε → 0≤R₀ → ε≤c*min L (Real.sqrt (L*Δ)) →
      Hardness (conservativeClass (μ:=L/κ) (L:=L) (ρ:=θ*(L/κ)) (Δ:=Δ)
        (R₀:=R₀) (σf:=σf) (σg:=σg)) ε
        (cq*ChiRefinementRates.deterministic L θ κ Δ ε/(Real.log (2+θ))^q) := by
  obtain ⟨t,η,ζ,cn,CR,Km,Cgap,η₀,bStar,Cf,CT,c,ht,ht1,hη,hη1,hζ,hζsmall,hcn,hcn1,hlen,hCR,hCRcn,hKm,hCgap,
    hη₀,hη₀1,hbs,hbs1,hbsgap,hCf,hCT,hc,hc1,cRate,hcRate,q,hmain⟩ := physical_full_oracle_rate_witness
  refine ⟨CT,c,cRate,hCT,hc,hc1,hcRate,q,?_⟩
  intro L κ θ Δ ε R₀ σf σg hL hκ hθκ hbranch hΔ hε hR₀ hacc
  obtain ⟨hJ,hS,hn,hm,hr,hrη,hcount,P,hPc,hPℓ,hPβ,hPθ,hcore,dim,hdim,hAll,hT,hF,hRate,hfamily⟩ :=
    hmain L κ θ Δ ε hL hκ hθκ hbranch hΔ hε hacc
  apply physical_conservative_hardness _ _ _ dim _ cn _ _ hdim hAll hT _ _ 3 1 ζ CR Km _ P
    _ _ _ _ _ _ _ _ _ _ hF (L/κ) L (θ*(L/κ)) Δ R₀ σf σg _ ε _ hR₀ _ hRate
  intro a
  obtain ⟨Pr,hf,hExt,hExt2,hg,r,hgap,hzero,hresponse,hmean,hunique,hmean0,hbarrier,hFull⟩ := hfamily a
  exact ⟨Pr,r,hzero,hgap,hmean,hExt,hFull⟩

end Bilevel.TransportHierarchy
