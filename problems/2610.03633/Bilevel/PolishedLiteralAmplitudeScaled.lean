import Bilevel.PolishedLiteralAmplitudeSource

/-! The source's fixed prefactor eta may be any value in (0,1]. Its
multiscale schedule still uses theta/alpha, independently of eta. -/
noncomputable section
set_option maxHeartbeats 1800000
namespace Bilevel.PolishedLiteral
open PrimitiveGeometry ZeroChainSchedule ZeroChainResidualBounds
open PolishedLiteralCompensated
open MultiscaleMean (const_mul_jet_norm)

/-- Source fb:lem:multiscale, for the stronger selected literal residual
family. The constant and normal-core threshold are universal; no upper
bound on v=theta/alpha or beta*v is used. -/
theorem actual_literal_amplitude_budgets_scaled : ∃ C τ : ℝ,1≤C ∧ 0<τ ∧
    ∀ (X U : Type*) [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
      [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
      (P : Parameters (X:=X) (U:=U)) (Lden α θ η : ℝ),
      0<Lden → 0<α → α≤1 → 1≤θ → 0<η → η≤1 → P.L=η*α*Lden → 0<P.μ → 0<P.β →
      P.β≤P.radius → P.β≤P.macroNode.width → P.macroNode.width≤P.macroNode.radius →
      P.J=levels (θ/α) → P.δ=resolution (1/64) P.β (θ/α) → P.w=width (1/64) P.β (θ/α) →
      (∀ y : PolishedLiteralCompensated.LowerSpace (Joint X U),
        ‖iteratedFDeriv ℝ 2 (P.amplitudePerturbation Lden) y‖≤C*P.μ*(P.β*Real.sqrt (α*θ)+α^2*P.β^2) ∧
        ‖iteratedFDeriv ℝ 3 (P.amplitudePerturbation Lden) y‖≤C*P.μ*(θ+α^2*P.β)) ∧
      (P.β*θ≤τ → ∀ z j,j≤P.J → |P.selectedResidual z/Lden|≤P.w j/4) := by
  obtain ⟨B,hB,hb⟩ := selected_residual_joint_jet_bounds
  obtain ⟨K,hK,hk⟩ := actual_literal_coupling_bounds
  obtain ⟨D,hD,hd⟩ := selected_residual_value_bound
  let C := 4*B^2+4096*K
  let τ := 1/(256*D)
  have hB0 : 0≤B := by linarith
  have hK0 : 0≤K := by linarith
  have hD0 : 0<D := by linarith
  have hC : 1≤C := by dsimp [C];nlinarith [sq_nonneg B]
  have hBC : 4*B^2≤C := by dsimp [C];linarith
  have hKC : 4096*K≤C := by dsimp [C];nlinarith [sq_nonneg B]
  refine ⟨C,τ,hC,by dsimp [τ];positivity,?_⟩
  intro X U _ _ _ _ _ _ P Lden α θ η hLd hα hα1 hθ hη hη1 hell hμ hβ hR hβb hbR hJ hδ hw
  have hL : 0<P.L := by rw [hell];positivity
  have hθ0 : 0<θ := by linarith
  have hv : 1≤θ/α := (le_div_iff₀ hα).mpr (by linarith)
  have hroot : α*Real.sqrt (θ/α)=Real.sqrt (α*θ) := by
    have h1 := Real.sq_sqrt (show 0≤θ/α by positivity)
    have h2 := Real.sq_sqrt (show 0≤α*θ by positivity)
    have hs : (α*Real.sqrt (θ/α))^2=(Real.sqrt (α*θ))^2 := by
      rw [mul_pow,h1,h2]
      field_simp
      ring
    nlinarith [Real.sqrt_nonneg (θ/α),Real.sqrt_nonneg (α*θ),mul_nonneg hα.le (Real.sqrt_nonneg (θ/α))]
  constructor
  · intro y
    have hcomp := P.compensation_bounds B hB0 hμ hL hβ
      (fun z k => hb X U P hL.le hβ hR hβb hbR z k.val (by omega)) y
    have hcoupl := hk X U P (1/64) (θ/α) (by norm_num) (by norm_num) hv hL hβ hR hβb hbR hJ hδ hw y
    have hbound (k : ℕ) (hk : k≤3) :
        ‖iteratedFDeriv ℝ k (P.amplitudePerturbation Lden) y‖≤
          (η*α)^2*‖iteratedFDeriv ℝ k P.compensation y‖+
            ((η*α)*(P.μ/P.L))*‖iteratedFDeriv ℝ k P.data.coupling y‖ := by
      rw [P.amplitudePerturbation_split Lden (η*α) hL.ne' hLd.ne' hell]
      have hf : ContDiff ℝ 3 (fun v => (η*α)^2*P.compensation v) := contDiff_const.mul P.compensation_contDiff
      have hg : ContDiff ℝ 3 (fun v => (η*α)*(P.μ/P.L)*P.data.coupling v) := contDiff_const.mul P.data.coupling_contDiff
      have hh := jet_sub_norm_le hf hg y k hk
      rw [const_mul_jet_norm P.compensation_contDiff _ y k hk,
        const_mul_jet_norm P.data.coupling_contDiff _ y k hk,
        abs_of_nonneg (sq_nonneg (η*α)),abs_of_pos (by positivity : 0<(η*α)*(P.μ/P.L))] at hh
      exact hh
    have hb2 := mul_le_mul_of_nonneg_left hcomp.1 (sq_nonneg (η*α))
    have hb3 := mul_le_mul_of_nonneg_left hcomp.2 (sq_nonneg (η*α))
    have hc2 := mul_le_mul_of_nonneg_left hcoupl.1 (show 0≤(η*α)*(P.μ/P.L) by positivity)
    have hc3 := mul_le_mul_of_nonneg_left hcoupl.2 (show 0≤(η*α)*(P.μ/P.L) by positivity)
    have he2 : (η*α)*(P.μ/P.L)*(K*P.L*P.β*Real.sqrt (θ/α)/(1/64:ℝ))=
        (64*K)*P.μ*P.β*(η*Real.sqrt (α*θ)) := by
      calc
        _=64*K*P.μ*P.β*(η*(α*Real.sqrt (θ/α))) := by field_simp;ring
        _=_ := by rw [hroot]
    have he3 : (η*α)*(P.μ/P.L)*(K*P.L*(θ/α)/(1/64:ℝ)^2)=4096*K*P.μ*(η*θ) := by
      field_simp
      ring
    rw [he2] at hc2
    rw [he3] at hc3
    have hηsq : η^2≤1 := by nlinarith
    have hηα : (η*α)^2≤α^2 := by nlinarith [mul_le_mul_of_nonneg_right hηsq (sq_nonneg α)]
    have hb2' := hb2.trans (mul_le_mul_of_nonneg_right hηα (show 0≤2*P.μ*B^2*P.β^2 by positivity))
    have hb3' := hb3.trans (mul_le_mul_of_nonneg_right hηα (show 0≤4*P.μ*B^2*P.β by positivity))
    have hc2' : (η*α)*(P.μ/P.L)*‖iteratedFDeriv ℝ 2 P.data.coupling y‖≤64*K*P.μ*P.β*Real.sqrt (α*θ) := by
      have hh := mul_le_mul_of_nonneg_left hη1 (show 0≤64*K*P.μ*P.β*Real.sqrt (α*θ) by positivity)
      nlinarith only [hc2,hh]
    have hc3' : (η*α)*(P.μ/P.L)*‖iteratedFDeriv ℝ 3 P.data.coupling y‖≤4096*K*P.μ*θ := by
      have hh := mul_le_mul_of_nonneg_left hη1 (show 0≤4096*K*P.μ*θ by positivity)
      nlinarith only [hc3,hh]
    constructor
    · have hBC2 : 2*B^2≤C := by nlinarith [sq_nonneg B]
      have hKC2 : 64*K≤C := by linarith
      have hcb := mul_le_mul_of_nonneg_right hBC2 (show 0≤P.μ*α^2*P.β^2 by positivity)
      have hck := mul_le_mul_of_nonneg_right hKC2 (show 0≤P.μ*P.β*Real.sqrt (α*θ) by positivity)
      have hh := hbound 2 (by norm_num)
      nlinarith only [hh,hb2',hc2',hcb,hck]
    · have hcb := mul_le_mul_of_nonneg_right hBC (show 0≤P.μ*α^2*P.β by positivity)
      have hck := mul_le_mul_of_nonneg_right hKC (show 0≤P.μ*θ by positivity)
      have hh := hbound 3 (by norm_num)
      nlinarith only [hh,hb3',hc3',hcb,hck]
  · intro hs z j hj
    have hr := hd X U P hL.le z
    have hres : |P.selectedResidual z/Lden|≤D*α*P.β^2 := by
      rw [abs_div,abs_of_pos hLd]
      apply (div_le_iff₀ hLd).mpr
      rw [hell] at hr
      have hηbound := mul_le_mul_of_nonneg_left hη1 (show 0≤D*α*P.β^2*Lden by positivity)
      nlinarith only [hr,hηbound]
    have hsmall : 4*D*P.β*θ≤(1/64:ℝ) := by
      have hh := (le_div_iff₀ (by positivity : 0<256*D)).mp hs
      dsimp only [τ] at hs
      nlinarith only [hh]
    have hf := (final_width_bounds (1/64) P.β (θ/α) (by norm_num) hβ.le hv).1
    have hm := width_antitone (1/64) P.β (θ/α) (by norm_num) hβ.le hv j (levels (θ/α)) (by simpa only [hJ] using hj)
    have hn : D*α*P.β^2≤((1/64:ℝ)*P.β/(θ/α))/4 := by
      apply (le_div_iff₀ (by norm_num : (0:ℝ)<4)).mpr
      apply (le_div_iff₀ (by positivity : 0<θ/α)).mpr
      have hh := mul_le_mul_of_nonneg_right hsmall hβ.le
      have he : 4*(D*α*P.β^2)*(θ/α)=4*D*P.β^2*θ := by field_simp;ring
      nlinarith only [hh,he]
    rw [hw]
    exact hres.trans (hn.trans (by linarith))

end Bilevel.PolishedLiteral
