import Bilevel.MultiscaleExpectedDimension
import Bilevel.MultiscaleInnerCertificate
import Bilevel.MultiscaleBoundedGapActualRate

/-! The bounded-gap, large-condition-number branch on the full
curvature-class accuracy window. The rate is for the literal original
full-query SFO execution and the same retained primitive family. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
universe u v
namespace Bilevel.MultiscaleMean
open CompensatedMean SingleFrameSource ChiHierarchyIndex ChiHierarchyHaar

def innerRate (L Δ κ θ ε σ : ℝ) : ℝ :=
  L*κ^2*Δ/ε^2+L^3*θ^2*κ^8*σ^2*Δ/ε^6

theorem bounded_gap_expected_witness : ∃ A K η C c cq : ℝ,
    1≤A ∧ 1≤K ∧ 0<η ∧ η≤1 ∧ 1≤C ∧ 0<c ∧ c≤1 ∧ 0<cq ∧
    ∀ (L Δ κ θ ε σ : ℝ),0<L → 0<Δ → Δ≤L → 2*A≤κ →
      1≤θ → θ≤κ → 0<ε → ε≤c*min L (κ*Real.sqrt (L*Δ)) →
      ∀ D₀ : ℕ,∃ D n : ℕ,∃ P : Parameters (E:=EuclideanGaussian.Space D) n,
      ∃ hD : ∀ i : FrameIndex (counts n) 0,chainSize i+1≤D,
        D₀≤D ∧ P.μ=2*(L/κ) ∧ P.L=L/A ∧ P.η=η ∧ P.c=1/64 ∧
        P.β=innerWidth A η ε κ L ∧ P.θ=θ ∧ P.R=K*P.β*Real.sqrt (n+1:ℕ) ∧
        P.β*P.θ≤1 ∧ 256≤n+1 ∧ n+1=innerLength η L Δ P.β ∧
        InnerRateProperty.{u,v} P hD (P.activationProbability σ) (P.activationProbability_le_one σ)
          ε (cq*innerRate L Δ κ θ ε σ) ∧
        (∀ a,InnerPrimitiveCertificate (P.withFrame (frame hD a (Sum.inl ())))
          (L/κ) L ((L/κ)*θ) Δ C κ ε) := by
  obtain ⟨A,K,η,C,c,hA,hK,hη,hη1,hC,hc,hc1,hfamily⟩ := bounded_gap_witness.{0}
  let rq := (η/(2048*A^4))/(2048*envelopeConstant ℝ*A^4/η^2)^2
  let cq := rq/512
  have hAp : 0<A := by linarith
  have hCp : 0<envelopeConstant ℝ := lt_of_lt_of_le zero_lt_one (envelopeConstant_one_le ℝ)
  have hcq : 0<cq := by dsimp [cq,rq];positivity
  refine ⟨A,K,η,C,c,cq,hA,hK,hη,hη1,hC,hc,hc1,hcq,?_⟩
  intro L Δ κ θ ε σ hL hΔ hΔL hκ hθ hθκ hε hacc D₀
  have hκp : 0<κ := by linarith
  let β := innerWidth A η ε κ L
  let T := innerLength η L Δ β
  let n := T-1
  obtain ⟨hβ,hβθ,hT,hn,hcount,hactual⟩ := hfamily L Δ κ θ ε hL hΔ hΔL hκ hθ hθκ hε hacc
  change 0<β at hβ
  have hμ : 0<2*(L/κ) := by positivity
  have hL' : 0<L/A := by positivity
  let proto := innerParameters n (2*(L/κ)) (L/A) η β θ K hμ hL' hη.le hη1 hβ hθ hK
    (LinearIsometryEquiv.refl ℝ (ZeroChain.Space n)).toLinearIsometry
  let p := proto.activationProbability σ
  obtain ⟨D,hD,hD₀,hExp⟩ := exists_inner_expected_dimension.{u,v} n D₀ proto.R proto.signalResolution p ε
    (proto.β_pos.trans_le proto.β_le_R) proto.signalResolution_pos
    (proto.activationProbability_pos σ) (proto.activationProbability_le_one σ) hε
  let P := innerParameters n (2*(L/κ)) (L/A) η β θ K hμ hL' hη.le hη1 hβ hθ hK
    (frame hD (fun _ => 1) (Sum.inl ()))
  have hcert (a : Orientations (counts n) 0 D) :
      InnerPrimitiveCertificate (P.withFrame (frame hD a (Sum.inl ()))) (L/κ) L ((L/κ)*θ) Δ C κ ε := by
    obtain ⟨Q,r,hf,hg,hr,hmean,hzero,hgap,hcoerc,hcurv,hblind⟩ :=
      hactual (EuclideanGaussian.Space D) (frame hD a (Sum.inl ()))
    refine ⟨Q,r,hf,hg,hr,hmean,hzero,hgap,hcoerc,hcurv,?_⟩
    have hgain : P.L/P.μ=κ/(2*A) := by dsimp [P,innerParameters];field_simp;ring
    intro x hx
    apply hblind x
    simpa only [Parameters.withFrame,hgain] using hx
  have he := @hExp P rfl rfl (fun a x hx => (hcert a).barrier x hx)
  have hnt : n+1=T := hn
  have hcount' : (η/(2048*A^4))*L*κ^2*Δ/ε^2≤((n+1:ℕ):ℝ) := by rwa [hnt]
  have hrate := actual_inner_probability_rate P hA hη hη1 hL hΔ hκp
    (show 0<θ by linarith) hε rfl rfl rfl (σ:=σ) hcount'
  change rq*innerRate L Δ κ θ ε σ≤((n+1:ℕ):ℝ)*(P.activationProbability σ)⁻¹ at hrate
  have hcost : cq*innerRate L Δ κ θ ε σ≤((n+1:ℕ):ℝ)/(512*(P.activationProbability σ)) := by
    have hh := div_le_div_of_nonneg_right hrate (by norm_num : (0:ℝ)≤512)
    convert hh using 1 <;> dsimp [cq] <;> simp only [div_eq_mul_inv,mul_inv_rev] <;> ring
  have he' : InnerRateProperty.{u,v} P hD (P.activationProbability σ) (P.activationProbability_le_one σ)
      ε (cq*innerRate L Δ κ θ ε σ) :=
    @innerRateProperty_mono.{u,v} n D P hD _ _ ε _ _ he hcost
  refine ⟨D,n,P,hD,hD₀,rfl,rfl,rfl,rfl,rfl,rfl,rfl,hβθ,?_,hn,he',hcert⟩
  rw [hnt]
  exact hT

end Bilevel.MultiscaleMean
