import NCConcave16991.ConeClockGap
import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-! # Exact maximization over the genuine Euclidean dual ball -/

noncomputable section

open Set Metric
open scoped BigOperators InnerProductSpace

namespace NCConcave16991.ConeValue

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem ball_affine_upper {R : ℝ} (hR : 0 < R) (base : ℝ) (r y : H)
    (hy : y ∈ closedBall 0 R) :
    base + R⁻¹ * ⟪r, y⟫_ℝ ≤ base + ‖r‖ := by
  have hy' : ‖y‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hy
  have hi := (real_inner_le_norm r y).trans
    (mul_le_mul_of_nonneg_left hy' (norm_nonneg r))
  have hh := mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hR.le)
  have he : R⁻¹ * (‖r‖ * R) = ‖r‖ := by field_simp [hR.ne']
  linarith only [hh, he]

theorem ball_affine_attains {R : ℝ} (hR : 0 < R) (base : ℝ) (r : H) :
    ∃ y ∈ closedBall 0 R, base + R⁻¹ * ⟪r, y⟫_ℝ = base + ‖r‖ := by
  by_cases hr : r = 0
  · subst r
    refine ⟨0, ?_, ?_⟩
    · simpa only [mem_closedBall, dist_self] using hR.le
    · simp
  · have hn : 0 < ‖r‖ := norm_pos_iff.mpr hr
    refine ⟨(R / ‖r‖) • r, ?_, ?_⟩
    · have hnorm : ‖(R / ‖r‖) • r‖ = R := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hR hn), div_mul_cancel₀ _ hn.ne']
      simpa only [mem_closedBall, dist_zero_right, hnorm] using (le_rfl : R ≤ R)
    · rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp [hR.ne', hn.ne']

/-- The constrained maximum is proved by its literal witness and Cauchy-Schwarz;
it is not an unconstrained-dual elimination assumption. -/
theorem ball_affine_sSup {R : ℝ} (hR : 0 < R) (base : ℝ) (r : H) :
    sSup ((fun y : H ↦ base + R⁻¹ * ⟪r, y⟫_ℝ) '' closedBall 0 R) = base + ‖r‖ := by
  obtain ⟨y, hy, he⟩ := ball_affine_attains hR base r
  have hb : BddAbove ((fun y : H ↦ base + R⁻¹ * ⟪r, y⟫_ℝ) '' closedBall 0 R) := by
    refine ⟨base + ‖r‖, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    exact ball_affine_upper hR base r w hw
  apply le_antisymm
  · apply csSup_le (show ((fun y : H ↦ base + R⁻¹ * ⟪r, y⟫_ℝ) '' closedBall 0 R).Nonempty from
      ⟨_, ⟨y, hy, rfl⟩⟩)
    rintro _ ⟨w, hw, rfl⟩
    exact ball_affine_upper hR base r w hw
  · exact le_csSup hb ⟨y, hy, he⟩

/-- Every maximizing unit-ball multiplier is the normalized residual when
the residual is nonzero. This follows from equality in the actual support
bound, without assuming a Danskin or Clarke representation. -/
theorem unit_multiplier_eq_normalized {r a : H} (hr : r ≠ 0) (ha : ‖a‖ ≤ 1)
    (he : ⟪r, a⟫_ℝ = ‖r‖) : a = ‖r‖⁻¹ • r := by
  have hn : 0 < ‖r‖ := norm_pos_iff.mpr hr
  have hnorm : ‖‖r‖⁻¹ • r‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
  have hi : ⟪a, ‖r‖⁻¹ • r⟫_ℝ = 1 := by
    have har : ⟪a, r⟫_ℝ = ‖r‖ := (real_inner_comm _ _).trans he
    rw [real_inner_smul_right, har, inv_mul_cancel₀ hn.ne']
  have hs : ‖a - ‖r‖⁻¹ • r‖ ^ 2 ≤ 0 := by
    rw [norm_sub_sq_real, hnorm, hi]
    nlinarith [norm_nonneg a]
  have hz : a - ‖r‖⁻¹ • r = 0 := by
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (a - ‖r‖⁻¹ • r)]
  exact sub_eq_zero.mp hz

theorem ball_maximizer_multiplier {R : ℝ} (hR : 0 < R) (base : ℝ) (r y : H)
    (hy : y ∈ closedBall 0 R)
    (hmax : base + R⁻¹ * ⟪r, y⟫_ℝ =
      sSup ((fun w : H ↦ base + R⁻¹ * ⟪r, w⟫_ℝ) '' closedBall 0 R)) :
    ‖R⁻¹ • y‖ ≤ 1 ∧
      (r ≠ 0 → R⁻¹ • y = ‖r‖⁻¹ • r) := by
  have hyn : ‖y‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hy
  have ha : ‖R⁻¹ • y‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
    have hh := mul_le_mul_of_nonneg_left hyn (inv_nonneg.mpr hR.le)
    simpa only [inv_mul_cancel₀ hR.ne'] using hh
  refine ⟨ha, ?_⟩
  intro hr
  apply unit_multiplier_eq_normalized hr ha
  rw [real_inner_smul_right]
  rw [ball_affine_sSup hR] at hmax
  linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def sourceMean {n M : ℕ} (w : Fin n → Fin (M + 1) → E) (j : Fin (M + 1)) : E :=
  (Real.sqrt (n : ℝ))⁻¹ • ∑ i, w i j

theorem sourceMean_unit {n M : ℕ} (hn : 0 < n) (w : Fin n → Fin (M + 1) → E)
    (hw : ∀ j, Orthonormal ℝ (fun i ↦ w i j)) (j : Fin (M + 1)) :
    ‖sourceMean w j‖ = 1 := by
  classical
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : ‖∑ i, w i j‖ ^ 2 = (n : ℝ) := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    simp_rw [inner_sum, orthonormal_iff_ite.mp (hw j)]
    simp
  have hnorm : ‖sourceMean w j‖ ^ 2 = 1 := by
    rw [sourceMean, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inv_pow,
      Real.sq_sqrt hnr.le, hs]
    exact inv_mul_cancel₀ hnr.ne'
  nlinarith only [hnorm, norm_nonneg (sourceMean w j)]

theorem average_scaled_row {n M : ℕ} (hn : 0 < n)
    (w : Fin n → Fin (M + 1) → E) (j : Fin (M + 1)) :
    (n : ℝ)⁻¹ • ∑ i, Real.sqrt (n : ℝ) • w i j = sourceMean w j := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hroot : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnr
  have hsq := Real.sq_sqrt hnr.le
  rw [← Finset.smul_sum, smul_smul, sourceMean]
  congr 1
  apply mul_right_cancel₀ hroot.ne'
  have he : (n : ℝ)⁻¹ * (n : ℝ) = 1 := inv_mul_cancel₀ hnr.ne'
  have hi : (Real.sqrt (n : ℝ))⁻¹ * Real.sqrt (n : ℝ) = 1 := inv_mul_cancel₀ hroot.ne'
  rw [mul_assoc, ← pow_two, hsq, he, hi]

end NCConcave16991.ConeValue
