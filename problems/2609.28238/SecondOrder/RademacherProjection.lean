import SecondOrder.RademacherMoments
import SecondOrder.OjaStep

open MeasureTheory
open scoped BigOperators InnerProductSpace Classical

namespace SecondOrder
noncomputable section

/-- A finite second-moment argument written as a pointwise polynomial
inequality. It applies to any finite probability law, not just fair signs. -/
theorem pmfMean_large_value_probability {α : Type*} [Fintype α]
    (p : PMF α) (X : α → ℝ) {m : ℝ} (hm : 0 < m)
    (hmean : pmfMean p X = m) (hsecond : pmfMean p (fun a => X a ^ 2) ≤ 3*m^2) :
    (1 : ℝ)/12 ≤ pmfMean p (fun a => if m/2 ≤ X a then (1 : ℝ) else 0) := by
  have hpoint (a : α) : 12*m*X a - X a^2 - 6*m^2 ≤
      36*m^2*(if m/2 ≤ X a then (1 : ℝ) else 0) := by
    split_ifs with ha
    · nlinarith [sq_nonneg (X a - 6*m), sq_nonneg m]
    · have hx := mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge ha))
        (show 0 ≤ 12*m by positivity)
      nlinarith [sq_nonneg (X a)]
  have h := pmfMean_mono p hpoint
  simp only [pmfMean_sub, pmfMean_mul, pmfMean_const, hmean] at h
  have hmul : m^2 * ((1:ℝ)/12) ≤
      m^2 * pmfMean p (fun a => if m/2 ≤ X a then (1 : ℝ) else 0) := by
    nlinarith
  exact (mul_le_mul_left (sq_pos_of_pos hm)).mp hmul

theorem signLaw_real_indicator {d : ℕ} (S : Set (Fin d → Bool)) :
    (signLaw d).real S = uniformMean (fun w => if w ∈ S then (1 : ℝ) else 0) := by
  have hS : MeasurableSet S := Set.Finite.measurableSet (Set.toFinite S)
  rw [← integral_signLaw]
  have he : (fun w => if w ∈ S then (1 : ℝ) else 0) = S.indicator (fun _ => (1:ℝ)) := rfl
  rw [he, integral_indicator_const (1:ℝ) hS]
  simp

/-- A fresh sign vector sees at least half the projection's second moment
with probability at least 1/12, in every nonzero deterministic direction. -/
theorem rademacherVector_projection_probability {d : ℕ} (g : Point d) (hg : g ≠ 0) :
    (1 : ℝ)/12 ≤ (signLaw d).real
      {w | ‖g‖^2/2 ≤ ⟪g, rademacherVector w⟫_ℝ ^ 2} := by
  rw [signLaw_real_indicator]
  apply pmfMean_large_value_probability (PMF.uniformOfFintype _)
    (fun w => ⟪g, rademacherVector w⟫_ℝ ^ 2) (sq_pos_of_pos (norm_pos_iff.mpr hg))
  · exact rademacherVector_second g
  · have h := rademacherVector_fourth g
    simpa only [uniformMean, ← pow_mul] using h

def rademacherInit {d : ℕ} (w : Fin d → Bool) : Point d :=
  normalizeProbe (rademacherVector w)

theorem rademacherVector_ne_zero {d : ℕ} (hd : 0 < d) (w : Fin d → Bool) :
    rademacherVector w ≠ 0 := by
  intro he
  have h := rademacherVector_norm_sq w
  rw [he, norm_zero, zero_pow (by decide : 2 ≠ 0)] at h
  have : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  linarith

theorem rademacherInit_norm {d : ℕ} (hd : 0 < d) (w : Fin d → Bool) :
    ‖rademacherInit w‖ = 1 :=
  normalizeProbe_norm (rademacherVector_ne_zero hd w)

theorem rademacherInit_measurable (d : ℕ) : Measurable (@rademacherInit d) :=
  measurable_of_finite _

theorem rademacherInit_inner_sq {d : ℕ} (g : Point d) (w : Fin d → Bool) :
    ⟪g, rademacherInit w⟫_ℝ ^ 2 = ⟪g, rademacherVector w⟫_ℝ ^ 2 / d := by
  simp only [rademacherInit, normalizeProbe, inner_smul_right, mul_pow, inv_pow,
    rademacherVector_norm_sq, div_eq_mul_inv]
  ring

theorem rademacherInit_projection_probability {d : ℕ} (hd : 0 < d)
    (g : Point d) (hg : g ≠ 0) :
    (1 : ℝ)/12 ≤ (signLaw d).real
      {w | ‖g‖^2/(2*d) ≤ ⟪g, rademacherInit w⟫_ℝ ^ 2} := by
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have he : {w | ‖g‖^2/(2*d) ≤ ⟪g, rademacherInit w⟫_ℝ ^ 2} =
      {w | ‖g‖^2/2 ≤ ⟪g, rademacherVector w⟫_ℝ ^ 2} := by
    ext w
    simp only [Set.mem_setOf_eq, rademacherInit_inner_sq, ← div_div,
      div_le_div_iff_of_pos_right hd']
  rw [he]
  exact rademacherVector_projection_probability g hg

end
end SecondOrder
