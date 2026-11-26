import Bilevel.ChiCurvatureFamily
import Bilevel.ChiBoundedKappaCurvatureRate
import Bilevel.ChiFixedVariableFullOracleRate

/-! Actual hard-family branches, with construction details retained in
the compact family certificates and all numerical constants public. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Bilevel.ChiCurvatureLower
open ChiExtensionCalibration MultiscaleMean
universe u v

theorem bounded_gap_family : ∃ A C c cq : ℝ,
    1≤A ∧ 1≤C ∧ 0<c ∧ c≤1 ∧ 0<cq ∧
    ∀ L μ Δ κ θ ε σ : ℝ,0<L → 0<μ → κ=L/μ → 0<Δ → Δ≤L → 2*A≤κ →
      1≤θ → θ≤κ → 0<ε → ε≤c*min L (κ*Real.sqrt (L*Δ)) →
      Family.{u,v} μ L (θ*μ) Δ C κ ε σ (cq*innerRate L Δ κ θ ε σ) := by
  obtain ⟨A,K,η,C,c,cq,hA,hK,hη,hη1,hC,hc,hc1,hcq,hmain⟩ := bounded_gap_expected_witness.{u,v}
  refine ⟨A,C,c,cq,hA,hC,hc,hc1,hcq,?_⟩
  intro L μ Δ κ θ ε σ hL hμ hκeq hΔ hΔL hκ hθ hθκ hε hacc
  obtain ⟨dim,n,P,hD,_hD,hpμ,hpL,hpη,hpc,hpβ,hpθ,hpR,hs,hn,hfloor,hRate,hP⟩ :=
    hmain L Δ κ θ ε σ hL hΔ hΔL hκ hθ hθκ hε hacc 0
  have hμeq : L/κ=μ := by rw [hκeq];field_simp
  left
  refine ⟨n,dim,P,hD,hs,hRate,?_⟩
  intro a
  simpa only [hμeq,mul_comm μ θ] using hP a

theorem bounded_kappa_family (Θ : ℝ) (hΘ : 2≤Θ) : ∃ C c cq : ℝ,
    1≤C ∧ 0<c ∧ c≤1 ∧ 0<cq ∧
    ∀ L μ Δ κ θ ε σ : ℝ,0<L → 0<μ → κ=L/μ → 0<Δ → 2≤κ → κ≤Θ →
      1≤θ → θ≤κ → 0<ε → ε≤c*min L (κ*Real.sqrt (L*Δ)) →
      Family.{u,v} μ L (θ*μ) Δ C κ ε σ (cq*innerRate L Δ κ θ ε σ) := by
  obtain ⟨t,η,ζ,cn,CR,Km,Cgap,η₀,bStar,Cf,c,Bs,Ccurv,ht,ht1,hη,hη1,hζ,hζsmall,hcn,hcn1,hlen,hCR,hCRcn,hKm,hCgap,hη₀,hη₀1,hbs,hbs1,hbsgap,hCf,hc,hc1,hBs,hCcurv,cRate,hcRate,hmain⟩ :=
    bounded_kappa_curvature_rate_witness.{u} Θ hΘ
  refine ⟨Ccurv,c,cRate,hCcurv,hc,hc1,hcRate,?_⟩
  intro L μ Δ κ θ ε σ hL hμ hκeq hΔ hκ hκΘ hθ hθκ hε hacc
  obtain ⟨hB,dim,hdim,hAll,hS,hn,hn₀,hrp,hratio,hcount,H,hRate,hd⟩ :=
    hmain L μ κ θ Δ ε σ hL hμ hκ hκeq hκΘ hθ hθκ hΔ hε hacc
  have hbig : CanonicalFamily.{u,v} μ L (θ*μ) Δ Ccurv κ ε σ
      (cRate*(L*(1+θ)*κ^2*Δ/ε^2+L^3*θ^2*(1+θ)*κ^8*σ^2*Δ/ε^6)) := by
    refine ⟨_,_,_,_,_,hdim,hAll,_,_,_,_,_,_,_,_,_,_,hB,H,hRate,?_⟩
    intro a
    obtain ⟨hv,hw,hb,hi12,hvir,P,hf,hg,r,hr0,hgap,hresponse,hmean,hunique,hzero,hbarrier,hcurv,hi,hsig,hO,hFull⟩ := hd a
    exact ⟨P,r,hr0,hgap,hmean,hcurv,hFull⟩
  right
  apply canonicalFamily_mono hL.le (le_refl _) _ hbig
  apply mul_le_mul_of_nonneg_left _ hcRate.le
  have hnonneg : 0≤ innerRate L Δ κ θ ε σ := by dsimp [innerRate];positivity
  calc
    innerRate L Δ κ θ ε σ≤(1+θ)*innerRate L Δ κ θ ε σ :=
      le_mul_of_one_le_left hnonneg (by linarith)
    _=L*(1+θ)*κ^2*Δ/ε^2+L^3*θ^2*(1+θ)*κ^8*σ^2*Δ/ε^6 := by dsimp [innerRate];ring

theorem large_gap_family : ∃ C c cq : ℝ,
    1≤C ∧ 0<c ∧ c≤1 ∧ 0<cq ∧
    ∀ L μ Δ κ θ ε σ : ℝ,0<L → 0<μ → κ=L/μ → L≤Δ → 2≤κ →
      1≤θ → θ≤κ → 0<ε → ε≤c*L →
      Family.{u,v} μ L (θ*μ) Δ C κ ε σ (cq*innerRate L Δ κ θ ε σ) := by
  obtain ⟨t,η,ζ,cn,CR,Km,Cgap,η₀,bStar,Cf,c,Ccurv,Bs,ht,ht1,hη,hη1,hζ,hζsmall,hcn,hcn1,hlen,hCR,hCRcn,hKm,hCgap,hη₀,hη₀1,hbs,hbs1,hbsgap,hCf,hc,hc1,hCcurv,hBs,cRate,hcRate,hmain⟩ :=
    fixed_variable_full_oracle_rate_witness.{u}
  refine ⟨Ccurv,c,cRate,hCcurv,hc,hc1,hcRate,?_⟩
  intro L μ Δ κ θ ε σ hL hμ hκeq hLΔ hκ hθ hθκ hε hacc
  have hΔ : 0<Δ := hL.trans_le hLΔ
  have hsqrt : L≤Real.sqrt (L*Δ) :=
    (Real.le_sqrt hL.le (by positivity)).mpr (by nlinarith only [hL,hLΔ])
  have hacc' : ε≤c*min L (Real.sqrt (L*Δ)) := by rwa [min_eq_left hsqrt]
  have hθκ2 : θ≤κ^2 := hθκ.trans (by nlinarith only [hκ])
  obtain ⟨hB,dim,hdim,hAll,hS,hn,hn₀,hrp,hratio,hcount,H,hRate,hd⟩ :=
    hmain L μ θ κ Δ ε σ hL hμ hθ hθκ2 hκ hκeq hΔ hε hacc'
  right
  refine ⟨_,_,_,_,_,hdim,hAll,_,_,_,_,_,_,_,_,_,_,hB,H,hRate,?_⟩
  intro a
  obtain ⟨hv,hw,hb,hi12,hvir,P,hf,hg,r,hr0,hgap,hresponse,hmean,hunique,hzero,hcurv,hbarrier,hi,hsig,hO,hFull⟩ := hd a
  exact ⟨P,r,hr0,hgap,hmean,hcurv,hFull⟩

end Bilevel.ChiCurvatureLower
