import Nonsmooth.RegularVectorCoordinateFamily
import Nonsmooth.PolynomialDensityMoments

open MeasureTheory Set
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem score_hessian_correction_polynomial_bound
    (s : ℝ → E →L[ℝ] ℝ) (H : ℝ → E →L[ℝ] E →L[ℝ] ℝ)
    {C D : ℝ} (hC : 0 ≤ C)
    (hs : ∀ x, ‖s x‖ ≤ C * (1 + |x| ^ 2))
    (hH : ∀ x, ‖H x‖ ≤ D * (1 + |x| ^ 4)) (x : ℝ) :
    ‖H x - (s x).smulRight (s x)‖ ≤ (D + 2 * C ^ 2) * (1 + |x| ^ 4) := by
  have hp := polynomial_growth_square (fun x => ‖s x‖) hC
    (fun x => by simpa only [abs_of_nonneg (norm_nonneg _)] using hs x) x
  norm_num only [show 2 * 2 = 4 from rfl] at hp
  rw [abs_of_nonneg (sq_nonneg _)] at hp
  have hn := norm_sub_le (H x) ((s x).smulRight (s x))
  rw [ContinuousLinearMap.norm_smulRight_apply, ← pow_two] at hn
  nlinarith [hH x]

theorem vectorCoordinate_growth_of_global_bounds
    (V : E → ℝ → ℝ) (s : E → ℝ → E →L[ℝ] ℝ)
    (H : E → ℝ → E →L[ℝ] E →L[ℝ] ℝ)
    {a B C D : ℝ} (ha : 0 < a) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hV : ∀ r x, a * x ^ 2 - B ≤ V r x)
    (hs : ∀ r x, ‖s r x‖ ≤ C * (1 + ‖r‖ + |x|))
    (hH : ∀ r x, ‖H r x‖ ≤ D * (1 + ‖r‖ ^ 2 + |x| ^ 2)) (t : E) :
    ∃ (a B C D : ℝ) (m l : ℕ), 0 < a ∧ ∀ r ∈ Metric.ball t 1, ∀ x,
      a * x ^ 2 - B ≤ V r x ∧ ‖s r x‖ ≤ C * (1 + |x| ^ m) ∧
        ‖H r x - (s r x).smulRight (s r x)‖ ≤ D * (1 + |x| ^ l) := by
  let T := ‖t‖ + 1
  let J := C * (2 + T)
  let K := D * (2 + T ^ 2)
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  have hJ : 0 ≤ J := by dsimp only [J]; positivity
  have hrT (r : E) (hr : r ∈ Metric.ball t 1) : ‖r‖ ≤ T := by
    have he := norm_add_le (r - t) t
    rw [sub_add_cancel] at he
    have hd : ‖r - t‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hr
    dsimp only [T]
    linarith
  have hs' (r : E) (hr : r ∈ Metric.ball t 1) (x : ℝ) : ‖s r x‖ ≤ J * (1 + |x| ^ 2) := by
    have hx : |x| ≤ 1 + |x| ^ 2 := by nlinarith [sq_nonneg (|x| - 1)]
    have hp : 1 + ‖r‖ + |x| ≤ (2 + T) * (1 + |x| ^ 2) := by
      nlinarith [hrT r hr, mul_nonneg hT (sq_nonneg |x|), sq_nonneg |x|]
    exact (hs r x).trans (by simpa only [J, mul_assoc] using mul_le_mul_of_nonneg_left hp hC)
  have hH' (r : E) (hr : r ∈ Metric.ball t 1) (x : ℝ) : ‖H r x‖ ≤ K * (1 + |x| ^ 4) := by
    have hr2 := (sq_le_sq₀ (norm_nonneg r) hT).mpr (hrT r hr)
    have hp : 1 + ‖r‖ ^ 2 + |x| ^ 2 ≤ (2 + T ^ 2) * (1 + |x| ^ 4) := by
      nlinarith [sq_nonneg (|x| ^ 2 - 1),
        mul_nonneg (sq_nonneg T) (pow_nonneg (abs_nonneg x) 4)]
    exact (hH r x).trans (by simpa only [K, mul_assoc] using mul_le_mul_of_nonneg_left hp hD)
  refine ⟨a, B, J, K + 2 * J ^ 2, 2, 4, ha, ?_⟩
  intro r hr x
  exact ⟨hV r x, hs' r hr x,
    score_hessian_correction_polynomial_bound (s r) (H r) hJ (hs' r hr) (hH' r hr) x⟩

def regularVectorCoordinateFamilyOfGrowth
    (V : E → ℝ → ℝ) (s : E → ℝ → E →L[ℝ] ℝ)
    (H : E → ℝ → E →L[ℝ] E →L[ℝ] ℝ)
    (hcV : Continuous (Function.uncurry V)) (hcs : Continuous (Function.uncurry s))
    (hcH : Continuous (Function.uncurry H))
    (hdV : ∀ r x, HasFDerivAt (fun r => V r x) (s r x) r)
    (hds : ∀ r x, HasFDerivAt (fun r => s r x) (H r x) r)
    {a B C D : ℝ} (ha : 0 < a) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hV : ∀ r x, a * x ^ 2 - B ≤ V r x)
    (hs : ∀ r x, ‖s r x‖ ≤ C * (1 + ‖r‖ + |x|))
    (hH : ∀ r x, ‖H r x‖ ≤ D * (1 + ‖r‖ ^ 2 + |x| ^ 2)) :
    RegularVectorCoordinateFamily V where
  score := s
  hessian := H
  potential_continuous := hcV
  score_continuous := hcs
  hessian_continuous := hcH
  potential_derivative := hdV
  score_derivative := hds
  growth := vectorCoordinate_growth_of_global_bounds V s H ha hC hD hV hs hH

end
end Nonsmooth
