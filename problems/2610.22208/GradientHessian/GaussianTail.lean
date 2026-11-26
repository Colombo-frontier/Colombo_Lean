import GradientHessian.GaussianSquare

/-! # Chi-square concentration under the actual product Gaussian law

This proves the first assertion of source `lem:sphere`, including the stated
constant `1/8`, by Gaussian density integration and exponential Markov.
-/

namespace GradientHessian.GaussianSquare

open MeasureTheory ProbabilityTheory Filter
noncomputable section

theorem exponential_chernoff (m : ℕ) {t : ℝ} (ht : t < 1 / 2) (a : ℝ) :
    (gaussianVector m).real {z | t * a ≤ t * energy z} ≤
      Real.exp (-t * a - (m : ℝ) / 2 * Real.log (1 - 2 * t)) := by
  have hset : {z : Fin m → ℝ | Real.exp (t*a) ≤ Real.exp (t * energy z)} =
      {z | t*a ≤ t * energy z} := by
    ext z
    simp only [Set.mem_setOf_eq, Real.exp_le_exp]
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := gaussianVector m) (f := fun z => Real.exp (t * energy z))
    (ae_of_all _ fun _ => (Real.exp_pos _).le)
    (energy_exponential_integrable m ht) (Real.exp (t*a))
  rw [hset, energy_exponential_integral_log m ht] at hmarkov
  have hbound : (gaussianVector m).real {z | t*a ≤ t*energy z} ≤
      Real.exp (-(m:ℝ)/2*Real.log (1-2*t)) / Real.exp (t*a) :=
    (le_div_iff₀ (Real.exp_pos (t*a))).2 (by simpa only [mul_comm] using hmarkov)
  convert hbound using 1
  rw [← Real.exp_sub]
  congr 1
  ring

theorem chi_square_upper_tail (m : ℕ) {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) :
    (gaussianVector m).real {z | (m : ℝ)*(1+u) ≤ energy z} ≤
      Real.exp (-(m : ℝ) * u ^ 2 / 8) := by
  let t := u / (2*(1+u))
  have hp : 0 < 1+u := by linarith
  have ht0 : 0 < t := div_pos hu (by positivity)
  have ht : t < 1/2 := by
    dsimp [t]
    apply (div_lt_iff₀ (by positivity : 0 < 2*(1+u))).2
    linarith
  have hset : {z : Fin m → ℝ | t*((m:ℝ)*(1+u)) ≤ t*energy z} =
      {z | (m:ℝ)*(1+u) ≤ energy z} := by
    ext z
    exact mul_le_mul_left ht0
  have h := exponential_chernoff m ht ((m:ℝ)*(1+u))
  rw [hset] at h
  have he : 1-2*t = (1+u)⁻¹ := by dsimp [t]; field_simp [ne_of_gt hp]; ring
  rw [he, Real.log_inv] at h
  have hexp : -t*((m:ℝ)*(1+u)) - (m:ℝ)/2*(-Real.log (1+u)) =
      (m:ℝ)/2 * (Real.log (1+u)-u) := by
    dsimp [t]
    field_simp [ne_of_gt hp]
    ring
  rw [hexp] at h
  apply h.trans
  apply Real.exp_le_exp.mpr
  have hlog := log_one_add_upper hu.le hu1
  have hmul := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ (m:ℝ)/2)
  nlinarith

theorem chi_square_lower_tail (m : ℕ) {u : ℝ} (hu : 0 < u) :
    (gaussianVector m).real {z | energy z ≤ (m : ℝ)*(1-u)} ≤
      Real.exp (-(m : ℝ) * u ^ 2 / 4) := by
  have ht : -u/2 < (1:ℝ)/2 := by linarith
  have htn : -u/2 < (0:ℝ) := by linarith
  have hset : {z : Fin m → ℝ | (-u/2)*((m:ℝ)*(1-u)) ≤ (-u/2)*energy z} =
      {z | energy z ≤ (m:ℝ)*(1-u)} := by
    ext z
    exact mul_le_mul_left_of_neg htn
  have h := exponential_chernoff m ht ((m:ℝ)*(1-u))
  rw [hset, show 1-2*(-u/2) = 1+u by ring] at h
  apply h.trans
  apply Real.exp_le_exp.mpr
  have hlog := log_one_add_lower hu.le
  have hmul := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ (m:ℝ)/2)
  nlinarith

/-- The manuscript's chi-square concentration statement, with all nondegenerate
parameter conditions explicit. The event is defined under a genuine probability
measure, not supplied as a numerical probability parameter. -/
theorem chi_square_two_sided {m : ℕ} (hm : 0 < m) {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    (gaussianVector m).real {z | u < |energy z / (m:ℝ) - 1|} ≤
      2 * Real.exp (-(m:ℝ) * u ^ 2 / 8) := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  let lower : Set (Fin m → ℝ) := {z | energy z ≤ (m:ℝ)*(1-u)}
  let upper : Set (Fin m → ℝ) := {z | (m:ℝ)*(1+u) ≤ energy z}
  have hsub : {z : Fin m → ℝ | u < |energy z/(m:ℝ)-1|} ⊆ lower ∪ upper := by
    intro z hz
    change u < |energy z/(m:ℝ)-1| at hz
    rcases lt_abs.mp hz with h | h
    · right
      have hd : 1+u < energy z/(m:ℝ) := by linarith
      have := (lt_div_iff₀ hm').mp hd
      dsimp [upper]
      nlinarith
    · left
      have hd : energy z/(m:ℝ) < 1-u := by linarith
      have := (div_lt_iff₀ hm').mp hd
      dsimp [lower]
      nlinarith
  have hlower := chi_square_lower_tail m hu
  have hupper := chi_square_upper_tail m hu hu1.le
  have hlower' : (gaussianVector m).real lower ≤ Real.exp (-(m:ℝ)*u^2/8) := by
    apply hlower.trans
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (Nat.cast_nonneg m : (0:ℝ) ≤ m) (sq_nonneg u)]
  calc
    _ ≤ (gaussianVector m).real (lower ∪ upper) := measureReal_mono hsub
    _ ≤ (gaussianVector m).real lower + (gaussianVector m).real upper := measureReal_union_le _ _
    _ ≤ _ := by linarith

end
end GradientHessian.GaussianSquare
