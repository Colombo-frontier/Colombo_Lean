import GradientHessian.ParameterOptimizationChoice

/-! The exact logical implication from the manuscript's uniform parameter
theorem to its main lower bound.  This module does not assume or assert a
proof of the parameter theorem itself. -/

noncomputable section
namespace GradientHessian.Model
open ParameterOptimization

/-- Integer rounding and optimization, with the full source quantifiers and
the exact minimax complexity.  The only premise is the stated parameter theorem. -/
theorem uniformParameterLowerBound_implies_mainLowerBound :
    UniformParameterLowerBound → MainLowerBound := by
  rintro ⟨CE, Cd, c₀, J₀, hCE, hCd, hc₀, hJ₀, hparameter⟩
  let E := CE + 1
  have hE1 : 1 ≤ E := by dsimp [E]; linarith
  have hE : 0 < E := by linarith
  have hCEE : CE ≤ E := by dsimp [E]; linarith
  let ζ : ℝ := 1 / (1 + 64 * E + 4 * Cd)
  have hden : 0 < 1 + 64 * E + 4 * Cd := by positivity
  have hζ : 0 < ζ := by dsimp [ζ]; positivity
  have hζ1 : ζ ≤ 1 := by
    dsimp [ζ]
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hζE : ζ * E ≤ 1 / 64 := by
    dsimp [ζ]
    rw [one_div_mul_eq_div]
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hζCd : Cd * ζ ≤ 1 / 4 := by
    dsimp [ζ]
    rw [mul_one_div]
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hζd : Cd * ζ ^ (3 / 2 : ℝ) ≤ 1 / 4 :=
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_self_of_le_one hζ.le hζ1 (by norm_num)) hCd.le).trans hζCd
  let m₀ := size J₀
  have hm₀1 : 1 ≤ m₀ := size_ge_one J₀
  have hm₀ : 0 < m₀ := by linarith
  let A := m₀ / ζ
  have hA : 0 < A := by dsimp [A]; positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let C := 4 * Cd + A ^ (3 / 2 : ℝ) / Real.log 2 + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hCdim : A ^ (3 / 2 : ℝ) / Real.log 2 ≤ C := by
    dsimp [C]
    linarith
  have hClog : 4 * Cd ≤ C := by
    have hp : 0 ≤ A ^ (3 / 2 : ℝ) / Real.log 2 := by positivity
    dsimp [C]
    linarith
  let a := ζ / (2 * m₀)
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : a < 1 := by
    dsimp [a]
    apply (div_lt_iff₀ (by positivity)).mpr
    linarith
  let c := c₀ * (Real.sqrt ζ / (16 * E))
  have hc : 0 < c := by
    have hs : 0 < Real.sqrt ζ := Real.sqrt_pos.2 hζ
    dsimp [c]
    positivity
  refine ⟨C, a, c, 1, hC, ha, ha1, hc, by norm_num, ?_⟩
  intro T d H hT hd _hH hHT
  have hTp : 0 < T := by linarith
  have hloglower : Real.log 2 ≤ Real.log (2 + T) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hlognonneg : 0 ≤ Real.log (2 + T) := hlog2.le.trans hloglower
  have hdA : A ^ (3 / 2 : ℝ) ≤ (d : ℝ) := by
    calc
      A ^ (3 / 2 : ℝ) = (A ^ (3 / 2 : ℝ) / Real.log 2) * Real.log 2 := by
        rw [div_mul_cancel₀ _ hlog2.ne']
      _ ≤ C * Real.log (2 + T) := mul_le_mul hCdim hloglower hlog2.le hC.le
      _ ≤ d := hd
  have hdimstart : m₀ ≤ ζ * (d : ℝ) ^ (2 / 3 : ℝ) := by
    have hp := Real.rpow_le_rpow (Real.rpow_nonneg hA.le _) hdA
      (by norm_num : (0 : ℝ) ≤ 2 / 3)
    rw [power_three_halves_two_thirds hA.le] at hp
    have hh := (div_le_iff₀ hζ).mp hp
    nlinarith
  have hHp : 0 < (H : ℝ) + 1 := by positivity
  have htstart : m₀ ≤ ζ * (T / ((H : ℝ) + 1)) := by
    have hh : (H : ℝ) + 1 ≤ (ζ * T) / (2 * m₀) := by
      convert hHT using 1
      dsimp [a]
      ring
    have hh' := (le_div_iff₀ (show 0 < 2 * m₀ by positivity)).mp hh
    have hpos : 0 ≤ m₀ * ((H : ℝ) + 1) := by positivity
    have hh'' : m₀ * ((H : ℝ) + 1) ≤ ζ * T := by nlinarith
    have ht := (le_div_iff₀ hHp).mpr hh''
    simpa only [mul_div_assoc] using ht
  have hstart : size J₀ ≤
      ζ * min ((d : ℝ) ^ (2 / 3 : ℝ)) (T / ((H : ℝ) + 1)) := by
    rw [mul_min_of_nonneg _ _ hζ.le]
    exact le_min hdimstart htstart
  have hlog : 4 * Cd * Real.log (2 + T) ≤ (d : ℝ) :=
    (mul_le_mul_of_nonneg_right hClog hlognonneg).trans hd
  obtain ⟨p⟩ := choice_exists J₀ hJ₀ d H hE1 hCd.le hζ hTp hζE hζd hstart hlog
  have hgap : CE * (8 : ℝ) ^ p.L * size p.J ≤ T := by
    calc
      CE * (8 : ℝ) ^ p.L * size p.J ≤ E * (8 : ℝ) ^ p.L * size p.J := by
        gcongr
        exact zero_le_one.trans (size_ge_one p.J)
      _ ≤ T := p.gap
  have hlower := hparameter p.J p.L d H T p.index p.height hgap p.dimension p.rich
  apply le_trans (ENNReal.ofReal_le_ofReal ?_) hlower
  have hr := mul_le_mul_of_nonneg_left p.rate hc₀.le
  dsimp [c]
  simpa only [mul_assoc] using hr

end GradientHessian.Model
