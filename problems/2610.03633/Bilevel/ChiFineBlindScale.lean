import Bilevel.ChiFineSourceScales
import Bilevel.ChiFineCouplingCore

/-! The actual finest normal width is bounded below at the physical
source scale, uniformly in the fine parameter and the public budgets. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration
open ZeroChainSchedule

theorem source_fine_blind_width {θ μ L η₀ η b K a Cf c : ℝ}
    (hθ : 0 < θ) (hμ : 0 < μ) (hL : 0 < L) (hη₀ : 0 < η₀)
    (hη : 0 < η) (hb : 0 < b) (hK : 0 < K) (ha : 0 < a) (hCf : 1 ≤ Cf)
    (hc : 0 < c) (hcs : c ≤ 1/128) (J : ℕ) (hJ : 1 ≤ J)
    (hv : 1 ≤ fineParameter (θ*μ) (3*μ/2) (η₀*L*a) (normalCoefficient L J) Cf J) :
    let v := fineParameter (θ*μ) (3*μ/2) (η₀*L*a) (normalCoefficient L J) Cf J
    6*c*η₀*η^J*b/(K*θ) ≤ width c (η^J*b/(K*a)) v (levels v) := by
  dsimp only
  let v := fineParameter (θ*μ) (3*μ/2) (η₀*L*a) (normalCoefficient L J) Cf J
  let P : ChiFine.Parameters := ⟨η₀*L*a,η^J*b/(K*a),v,c,by positivity,by positivity,hv,hc,hcs⟩
  have hlo := P.final_normal_width
  apply le_trans _ hlo.1
  change 6*c*η₀*η^J*b/(K*θ) ≤ c*(η^J*b/(K*a))/v
  have hCfpos : 0 < Cf := by linarith
  have hJpos : (0:ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  have hs : 0 < Real.sqrt (2*(J:ℝ)) := Real.sqrt_pos.mpr (by positivity)
  have he : c*(η^J*b/(K*a))/v =
      (6*c*η₀*η^J*b/(K*θ))*(Cf^(J+1)*((J:ℝ)+1)*Real.sqrt (2*(J:ℝ))) := by
    dsimp only [v]
    rw [fineParameter_source_formula hμ hL]
    field_simp
    ring
  rw [he]
  apply le_mul_of_one_le_right (by positivity)
  apply one_le_mul_of_one_le_of_one_le
  · exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hCf) (by have := Nat.cast_nonneg (α:=ℝ) J; linarith)
  · apply Real.one_le_sqrt.mpr
    have hj : (1:ℝ) ≤ J := by exact_mod_cast hJ
    linarith

end Bilevel.ChiExtensionCalibration
