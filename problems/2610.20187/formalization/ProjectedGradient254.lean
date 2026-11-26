import Projection254
import GradientSupport254
import Energy254

noncomputable section
open scoped RealInnerProductSpace BigOperators
namespace Paper254

def projectedGradientStep {d : ℕ} {D : ℝ} (W : Domain d D)
    (G α : ℝ) (f : Loss d) (z : W.carrier) : W.carrier :=
  metricProject W (ContinuousLinearEquiv.refl ℝ (Space d))
    (z.val-α • selectedGradient W G f z)

theorem projectedGradient_one_step {d : ℕ} {D G η α : ℝ} (W : Domain d D)
    (hη : 0 < η) (hα : 0 < α) {f : Loss d} (hf : AdmissibleLoss W G η f)
    (z u : W.carrier) :
    2*α*(f z.val-f u.val) ≤ ‖z.val-u.val‖^2 -
      ‖(projectedGradientStep W G α f z).val-u.val‖^2 + α^2*G^2 := by
  let g := selectedGradient W G f z
  let next := (projectedGradientStep W G α f z).val
  have hg := selectedGradient_spec W hf z
  have hp := metricProject_pythagorean W (ContinuousLinearEquiv.refl ℝ (Space d))
    (z.val-α • g) u
  change ‖u.val-next‖^2+‖z.val-α • g-next‖^2 ≤ ‖u.val-(z.val-α • g)‖^2 at hp
  have he : u.val-(z.val-α • g) = -((z.val-u.val)-α • g) := by abel
  rw [he, norm_neg, norm_sub_rev u.val next] at hp
  have hdist : ‖next-u.val‖^2 ≤ ‖(z.val-u.val)-α • g‖^2 := by
    nlinarith [sq_nonneg ‖z.val-α • g-next‖]
  have hs := gradient_support W hη hf.expConcave hg.1 z.property u.property
  have hsupport : f z.val-f u.val ≤ ⟪g,z.val-u.val⟫ := by
    simp only [inner_sub_right] at hs ⊢
    linarith
  have hn := norm_sub_sq_real (z.val-u.val) (α • g)
  simp only [real_inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos hα] at hn
  have hcomm : ⟪z.val-u.val,g⟫ = ⟪g,z.val-u.val⟫ := real_inner_comm _ _
  rw [hcomm] at hn
  have hgn : ‖g‖^2 ≤ G^2 := by
    have hh : ‖g‖ ≤ G := hg.2
    nlinarith [norm_nonneg g]
  have hmul := mul_le_mul_of_nonneg_left hgn (sq_nonneg α)
  have hreg := mul_le_mul_of_nonneg_left hsupport (show 0 ≤ 2*α by positivity)
  change 2*α*(f z.val-f u.val) ≤ ‖z.val-u.val‖^2-‖next-u.val‖^2+α^2*G^2
  nlinarith

theorem comparator_squared_distance_movement {d : ℕ} {D : ℝ}
    (W : Domain d D) (z u v : W.carrier) :
    ‖z.val-v.val‖^2-‖z.val-u.val‖^2 ≤ 2*D*‖v.val-u.val‖ := by
  have hzv := W.diameter z.val z.property v.val v.property
  have hzu := W.diameter z.val z.property u.val u.property
  have hd := norm_sub_norm_le (z.val-v.val) (z.val-u.val)
  have he : (z.val-v.val)-(z.val-u.val) = u.val-v.val := by abel
  rw [he, norm_sub_rev u.val v.val] at hd
  have h1 := mul_le_mul_of_nonneg_right hd
    (add_nonneg (norm_nonneg (z.val-v.val)) (norm_nonneg (z.val-u.val)))
  have h2 := mul_le_mul_of_nonneg_left (show ‖z.val-v.val‖+‖z.val-u.val‖ ≤ 2*D by linarith)
    (norm_nonneg (v.val-u.val))
  nlinarith

end Paper254
#print axioms Paper254.projectedGradient_one_step
#print axioms Paper254.comparator_squared_distance_movement
