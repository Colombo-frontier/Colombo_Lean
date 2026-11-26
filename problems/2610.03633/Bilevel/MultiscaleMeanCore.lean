import Bilevel.CompensatedMeanCore
import Bilevel.ZeroChainWrappedResidual
import Bilevel.WrappedRegularity

/-! The exact multiscale mean family, using the source schedule and the actual
carried residual. Its proposed response is stationary under an explicit
numerical smallness condition. No regularity or minimization conclusion is
inserted into the data as an assumption. -/

noncomputable section
namespace Bilevel.MultiscaleMean
open ZeroChain WrappedChain RadialWrapper ZeroChainSchedule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

structure Parameters (n : ℕ) where
  μ : ℝ
  L : ℝ
  η : ℝ
  β : ℝ
  θ : ℝ
  c : ℝ
  ν : ℝ
  R : ℝ
  U : Space n →ₗᵢ[ℝ] E
  μ_pos : 0 < μ
  L_pos : 0 < L
  η_nonneg : 0 ≤ η
  η_le_one : η ≤ 1
  β_pos : 0 < β
  θ_ge_one : 1 ≤ θ
  c_pos : 0 < c
  c_small : c ≤ 1/16
  ν_nonneg : 0 ≤ ν
  β_le_R : β ≤ R

namespace Parameters
variable {n : ℕ} (P : Parameters (E := E) n)

def amplitude : ℝ := P.η*P.L*P.β^2
def outer : E → ℝ := WrappedChain.value n P.amplitude P.β P.ν P.R P.U
def residual : E → ℝ := ZeroChainWrappedResidual.residual n P.amplitude P.β P.R P.U
def revealed (x : E) : ℝ := P.outer x-P.residual x
def pieces : ℕ → E → ℝ := ZeroChainWrappedResidual.piece n (levels P.θ)
  (resolution P.c 1 P.θ) P.amplitude P.β P.R P.U

omit [CompleteSpace E] in
theorem amplitude_nonneg : 0 ≤ P.amplitude := by
  have hη := P.η_nonneg
  have hL := P.L_pos
  dsimp [amplitude]
  positivity

theorem outer_contDiff : ContDiff ℝ 3 P.outer := by
  have hb : ContDiff ℝ 3 (bowl (E := E) P.ν P.R) := by
    apply contDiff_const.mul
    exact ((contDiff_const.add ((contDiff_norm_sq ℝ).div_const (P.R^2))).sqrt
      (fun u => (radicand_pos P.R u).ne')).sub contDiff_const
  exact ((ScaledZeroChain.value_contDiff n 3 P.amplitude P.β).comp
    (ZeroChainWrappedResidual.coordinates_contDiff n P.R P.U)).add hb

theorem residual_contDiff : ContDiff ℝ 3 P.residual :=
  ZeroChainWrappedResidual.residual_contDiff n P.amplitude P.β P.R P.U

theorem revealed_contDiff : ContDiff ℝ 3 P.revealed := P.outer_contDiff.sub P.residual_contDiff

theorem pieces_contDiff (j : ℕ) : ContDiff ℝ 3 (P.pieces j) :=
  ZeroChainWrappedResidual.piece_contDiff n (levels P.θ) (resolution P.c 1 P.θ)
    P.amplitude P.β P.R P.U j

theorem decomposition (u : E) :
    (∑ j ∈ Finset.range (levels P.θ+1),P.pieces j u) = P.residual u :=
  ZeroChainWrappedResidual.sum_piece n (levels P.θ) (resolution P.c 1 P.θ)
    P.amplitude P.β P.R P.U u

def data : CompensatedMean.Data (E := E) where
  μ := P.μ
  L := P.L
  J := levels P.θ
  r := P.residual
  A := P.revealed
  e := P.pieces
  w := width P.c P.β P.θ
  r_smooth := P.residual_contDiff
  A_smooth := P.revealed_contDiff
  e_smooth := P.pieces_contDiff
  w_pos := fun j _ => width_pos P.c P.β P.θ P.c_pos P.β_pos P.θ_ge_one j
  decomposition := P.decomposition

theorem actual_overlap (u : E) :
    (ZeroChainCarry.carriedActive n (levels P.θ) (resolution P.c 1 P.θ) P.amplitude
      (fun x => P.β⁻¹ • coordinates n P.R P.U x) u).card ≤ 3 :=
  ZeroChainWrappedResidual.source_carried_overlap n P.c P.θ P.amplitude P.β P.R
    P.c_pos P.c_small P.θ_ge_one P.U u

theorem exact_hyperobjective (x : E) :
    P.data.upper x (P.data.response x) = P.outer ((P.L/P.μ) • x) := by
  rw [P.data.hyperobjective_substitution x P.L_pos.ne']
  change P.outer ((P.L/P.μ) • x)-P.residual ((P.L/P.μ) • x)+P.residual ((P.L/P.μ) • x) = _
  ring

theorem core_width_condition {C : ℝ} (hC : 0 ≤ C)
    (hr : ∀ u, |P.residual u| ≤ C*P.amplitude)
    (hsmall : 4*C*P.β*P.θ ≤ P.c) (u : E) (j : ℕ) (hj : j ≤ levels P.θ) :
    |P.residual u/P.L| ≤ width P.c P.β P.θ j/4 := by
  have hθ : 0 < P.θ := by linarith [P.θ_ge_one]
  have hL := P.L_pos
  have hb : |P.residual u/P.L| ≤ C*P.β^2 := by
    rw [abs_div,abs_of_pos P.L_pos]
    apply (div_le_iff₀ P.L_pos).mpr
    apply (hr u).trans
    have hη := mul_le_mul_of_nonneg_left P.η_le_one
      (show 0 ≤ C*P.L*P.β^2 by positivity)
    dsimp [amplitude]
    nlinarith only [hη]
  have hw := (final_width_bounds P.c P.β P.θ P.c_pos.le P.β_pos.le P.θ_ge_one).1
  have hwj := width_antitone P.c P.β P.θ P.c_pos.le P.β_pos.le P.θ_ge_one j (levels P.θ) hj
  have hc : C*P.β^2 ≤ (P.c*P.β/P.θ)/4 := by
    apply (le_div_iff₀ (by norm_num : (0:ℝ) < 4)).mpr
    apply (le_div_iff₀ hθ).mpr
    nlinarith [mul_le_mul_of_nonneg_right hsmall P.β_pos.le]
  exact hb.trans (hc.trans (by linarith))

theorem actual_stationary_response {C : ℝ} (hC : 0 ≤ C)
    (hr : ∀ u, |P.residual u| ≤ C*P.amplitude)
    (hsmall : 4*C*P.β*P.θ ≤ P.c) (x : E) :
    HasGradientAt (P.data.lower x) 0 (P.data.response x) :=
  P.data.response_hasGradient_zero x P.μ_pos.ne' P.L_pos.ne'
    (P.core_width_condition hC hr hsmall)

theorem revealed_gradient (u : E) :
    gradient P.revealed u = gradient P.outer u-gradient P.residual u := by
  change gradient (fun x => P.outer x-P.residual x) u = _
  rw [gradient,fderiv_sub (P.outer_contDiff.differentiable (by norm_num) u)
    (P.residual_contDiff.differentiable (by norm_num) u),map_sub]
  rfl

theorem residual_gradient_bound {C : ℝ}
    (hr : ∀ u, ‖iteratedFDeriv ℝ 1 P.residual u‖ ≤ C*P.amplitude/P.β) (u : E) :
    ‖gradient P.residual u‖ ≤ C*P.amplitude/P.β := by
  have hh := hr u
  rw [← norm_iteratedFDeriv_fderiv (n:=0),norm_iteratedFDeriv_zero] at hh
  simpa only [gradient,LinearIsometryEquiv.norm_map] using hh

/-- The raw upper-gradient budget, before substituting the gap and radius
budgets. The η factor is preserved, which is essential for the raw Cf claim. -/
theorem upper_gradient_raw_bound (B C : ℝ) (hB : 0 ≤ B)
    (hchain : ∀ z : Space n, ∀ j, |gradient (ZeroChain.value n) z j| ≤ B)
    (hr : ∀ u, ‖iteratedFDeriv ℝ 1 P.residual u‖ ≤ C*P.amplitude/P.β)
    (x : E) (y : CompensatedMean.LowerSpace E) :
    ‖P.data.upperY x y‖ ≤
      P.amplitude/P.β*B*Real.sqrt (n+1:ℕ)+P.ν*P.R+C*P.amplitude/P.β+P.L := by
  have hR : 0 < P.R := P.β_pos.trans_le P.β_le_R
  have hH (u : E) : ‖gradient P.outer u‖ ≤ P.amplitude/P.β*B*Real.sqrt (n+1:ℕ)+P.ν*P.R := by
    rw [show P.outer = WrappedChain.value n P.amplitude P.β P.ν P.R P.U from rfl,
      (value_hasGradientAt n P.amplitude P.β P.ν P.R hR P.U u).gradient]
    exact wrappedGradient_bound P.ν P.R _ P.ν_nonneg hR u _
      (carriedGradient_norm_bound n P.amplitude P.β P.R B P.amplitude_nonneg P.β_pos hB hchain P.U u)
  have hA (u : E) : ‖gradient P.revealed u‖ ≤
      P.amplitude/P.β*B*Real.sqrt (n+1:ℕ)+P.ν*P.R+C*P.amplitude/P.β := by
    rw [P.revealed_gradient]
    exact (norm_sub_le _ _).trans (add_le_add (hH u) (P.residual_gradient_bound hr u))
  change ‖CompensatedMean.pack E (gradient P.revealed (CompensatedMean.uProj E y)) P.L 0‖ ≤ _
  have hb := CompensatedMean.pack_norm_le (gradient P.revealed (CompensatedMean.uProj E y)) P.L 0
  rw [abs_zero,add_zero,abs_of_pos P.L_pos] at hb
  exact hb.trans (add_le_add_right (hA _) P.L)

end Parameters

/-- A single numerical constant controls the actual residual in all ambient
dimensions. Its explicit width condition proves stationary response, rather
than assuming cutoff linearity at the proposed response. -/
theorem universal_stationary_response : ∃ C : ℝ, 1 ≤ C ∧
    ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      (n : ℕ) (P : Parameters (E := E) n), 4*C*P.β*P.θ ≤ P.c → ∀ x : E,
        HasGradientAt (P.data.lower x) 0 (P.data.response x) := by
  obtain ⟨C,hC,hb⟩ := ZeroChainWrappedResidual.residual_uniform_bounds
  refine ⟨C,hC,fun E _ _ _ n P hs x => ?_⟩
  apply P.actual_stationary_response (by linarith) _ hs x
  intro u
  exact (hb E n P.amplitude P.β P.R P.amplitude_nonneg P.β_pos P.β_le_R P.U u).1

end Bilevel.MultiscaleMean
