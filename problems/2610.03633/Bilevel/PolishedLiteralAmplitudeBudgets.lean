import Bilevel.PolishedLiteralPerturbationBudgets
import Bilevel.PolishedLiteralResponse

/-! Literal amplitude-aware lift: the residual amplitude ell=P.L is
independent of the lower coupling scale Lden. The exact exponential chain,
physical flattening and smooth normal features are those already defined.
The schedule is v=theta/alpha with ell=alpha*Lden. -/
noncomputable section
set_option maxHeartbeats 1800000
namespace Bilevel.PolishedLiteral
open PrimitiveGeometry ZeroChainSchedule ZeroChainResidualBounds
open PolishedLiteralCompensated
open MultiscaleMean (const_mul_jet_norm)
namespace Parameters
variable {X U : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
variable (P : Parameters (X:=X) (U:=U))

def amplitudePerturbation (Lden : ℝ) (y : PolishedLiteralCompensated.LowerSpace (Joint X U)) : ℝ :=
  P.μ/(2*Lden^2)*(P.selectedResidual (uProj (Joint X U) y))^2-
    P.μ/Lden*P.data.coupling y

theorem amplitudePerturbation_contDiff (Lden : ℝ) : ContDiff ℝ 3 (P.amplitudePerturbation Lden) :=
  (contDiff_const.mul ((P.selectedResidual_contDiff.comp (uProj (Joint X U)).contDiff).pow 2)).sub
    (contDiff_const.mul P.data.coupling_contDiff)

theorem amplitudePerturbation_formula (Lden : ℝ) (y : PolishedLiteralCompensated.LowerSpace (Joint X U)) :
    P.amplitudePerturbation Lden y=
      P.μ/(2*Lden^2)*(P.selectedResidual (uProj (Joint X U) y))^2-
        P.μ/Lden*(∑ j ∈ Finset.range (P.J+1),P.selectedPiece j (uProj (Joint X U) y)*
          PolishedLiteralCompensated.normal (P.w j) (sProj (Joint X U) y)) := rfl

theorem amplitudePerturbation_split (Lden α : ℝ) (hL : P.L≠0) (hLd : Lden≠0) (hell : P.L=α*Lden) :
    P.amplitudePerturbation Lden=fun y => α^2*P.compensation y-
      α*(P.μ/P.L)*P.data.coupling y := by
  funext y
  unfold amplitudePerturbation compensation
  field_simp
  rw [hell]
  ring

end Parameters

/-- Source fb:lem:multiscale, for the stronger selected literal residual
family. The constant and normal-core threshold are universal; no upper
bound on v=theta/alpha or beta*v is used. -/
theorem actual_literal_amplitude_budgets : ∃ C τ : ℝ,1≤C ∧ 0<τ ∧
    ∀ (X U : Type*) [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
      [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
      (P : Parameters (X:=X) (U:=U)) (Lden α θ : ℝ),
      0<Lden → 0<α → α≤1 → 1≤θ → P.L=α*Lden → 0<P.μ → 0<P.β →
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
  intro X U _ _ _ _ _ _ P Lden α θ hLd hα hα1 hθ hell hμ hβ hR hβb hbR hJ hδ hw
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
          α^2*‖iteratedFDeriv ℝ k P.compensation y‖+
            (α*(P.μ/P.L))*‖iteratedFDeriv ℝ k P.data.coupling y‖ := by
      rw [P.amplitudePerturbation_split Lden α hL.ne' hLd.ne' hell]
      have hf : ContDiff ℝ 3 (fun v => α^2*P.compensation v) := contDiff_const.mul P.compensation_contDiff
      have hg : ContDiff ℝ 3 (fun v => α*(P.μ/P.L)*P.data.coupling v) := contDiff_const.mul P.data.coupling_contDiff
      have hh := jet_sub_norm_le hf hg y k hk
      rw [const_mul_jet_norm P.compensation_contDiff _ y k hk,
        const_mul_jet_norm P.data.coupling_contDiff _ y k hk,
        abs_of_nonneg (sq_nonneg α),abs_of_pos (by positivity : 0<α*(P.μ/P.L))] at hh
      exact hh
    have hb2 := mul_le_mul_of_nonneg_left hcomp.1 (sq_nonneg α)
    have hb3 := mul_le_mul_of_nonneg_left hcomp.2 (sq_nonneg α)
    have hc2 := mul_le_mul_of_nonneg_left hcoupl.1 (show 0≤α*(P.μ/P.L) by positivity)
    have hc3 := mul_le_mul_of_nonneg_left hcoupl.2 (show 0≤α*(P.μ/P.L) by positivity)
    have he2 : α*(P.μ/P.L)*(K*P.L*P.β*Real.sqrt (θ/α)/(1/64:ℝ))=
        (64*K)*P.μ*P.β*Real.sqrt (α*θ) := by
      calc
        _=64*K*P.μ*P.β*(α*Real.sqrt (θ/α)) := by field_simp;ring
        _=_ := by rw [hroot]
    have he3 : α*(P.μ/P.L)*(K*P.L*(θ/α)/(1/64:ℝ)^2)=4096*K*P.μ*θ := by
      field_simp
      ring
    rw [he2] at hc2
    rw [he3] at hc3
    constructor
    · have hBC2 : 2*B^2≤C := by nlinarith [sq_nonneg B]
      have hKC2 : 64*K≤C := by linarith
      have hcb := mul_le_mul_of_nonneg_right hBC2 (show 0≤P.μ*α^2*P.β^2 by positivity)
      have hck := mul_le_mul_of_nonneg_right hKC2 (show 0≤P.μ*P.β*Real.sqrt (α*θ) by positivity)
      have hh := hbound 2 (by norm_num)
      nlinarith only [hh,hb2,hc2,hcb,hck]
    · have hcb := mul_le_mul_of_nonneg_right hBC (show 0≤P.μ*α^2*P.β by positivity)
      have hck := mul_le_mul_of_nonneg_right hKC (show 0≤P.μ*θ by positivity)
      have hh := hbound 3 (by norm_num)
      nlinarith only [hh,hb3,hc3,hcb,hck]
  · intro hs z j hj
    have hr := hd X U P hL.le z
    have hres : |P.selectedResidual z/Lden|≤D*α*P.β^2 := by
      rw [abs_div,abs_of_pos hLd]
      apply (div_le_iff₀ hLd).mpr
      rw [hell] at hr
      exact hr.trans_eq (by ring)
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
