import LowRank.GaussianMomentScaling
import Mathlib.Data.Real.Pi.Bounds

/-! Coarse quantitative bounds for Gaussian radial positive and negative moments. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix ENNReal
noncomputable section

theorem gaussianRadialMoment_le {m : ℕ} (hm : 0 < m) (q : ℕ) (v : NNReal) :
    gaussianRadialMoment m q v ≤
      ENNReal.ofReal (((v : ℝ) * ((m : ℝ) + 2 * q)) ^ q) := by
  rw [gaussianRadialMoment_formula hm q v, mul_pow]
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg v.coe_nonneg q)
  have h := Finset.prod_le_prod (s := Finset.range q)
    (f := fun j : ℕ => (m : ℝ) + 2 * j) (g := fun _ => (m : ℝ) + 2 * q)
    (fun j _ => by positivity) (fun j hj => by
      have hj' : (j : ℝ) ≤ q := by exact_mod_cast (Finset.mem_range.mp hj).le
      dsimp only
      linarith)
  simpa only [Finset.prod_const, Finset.card_range] using h

theorem reciprocalSquaredGaussianMoment_le {m q : ℕ} (hq : 2 * q < m) (v : NNReal) :
    reciprocalSquaredGaussianMoment m q v ≤
      ENNReal.ofReal (((v : ℝ)⁻¹ / ((m : ℝ) - 2 * q)) ^ q) := by
  have hpos : 0 < (m : ℝ) - 2 * q := by
    have h : 2 * (q : ℝ) < m := by exact_mod_cast hq
    linarith
  have hp : ((m : ℝ) - 2 * q) ^ q ≤
      ∏ j ∈ Finset.range q, ((m : ℝ) - 2 * (j + 1)) := by
    have h := Finset.prod_le_prod (s := Finset.range q)
      (f := fun _ => (m : ℝ) - 2 * q) (g := fun j : ℕ => (m : ℝ) - 2 * (j + 1))
      (fun _ _ => hpos.le) (fun j hj => by
        have hj' : (j : ℝ) + 1 ≤ q := by exact_mod_cast Finset.mem_range.mp hj
        dsimp only
        linarith)
    simpa only [Finset.prod_const, Finset.card_range] using h
  rw [reciprocalSquaredGaussianMoment_formula hq v, div_pow]
  apply ENNReal.ofReal_le_ofReal
  rw [div_eq_mul_inv]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (inv_nonneg.mpr v.coe_nonneg) q)
  exact inv_anti₀ (pow_pos hpos q) hp

theorem gaussianMomentFormula_two_neg_half_le :
    gaussianMomentFormula 2 (-(1 / 2)) ≤ 2 := by
  have hpow : (2 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hsqrt : Real.sqrt Real.pi ≤ 2 := (Real.sqrt_le_iff).2 ⟨by norm_num, by
    nlinarith [Real.pi_lt_four]⟩
  have he : gaussianMomentFormula 2 (-(1 / 2)) =
      (2 : ℝ) ^ (-(1 / 2 : ℝ)) * Real.sqrt Real.pi := by
    norm_num [gaussianMomentFormula, Real.Gamma_one_half_eq]
  rw [he]
  nlinarith [Real.sqrt_nonneg Real.pi]

theorem gaussianMomentFormula_one_half_ge :
    (1 / 2 : ℝ) ≤ gaussianMomentFormula 1 (1 / 2) := by
  have hsqrt : Real.sqrt Real.pi ≤ 2 := (Real.sqrt_le_iff).2 ⟨by norm_num, by
    nlinarith [Real.pi_lt_four]⟩
  have htwo : 1 ≤ Real.sqrt (2 : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by norm_num)
  have he : gaussianMomentFormula 1 (1 / 2) = Real.sqrt 2 / Real.sqrt Real.pi := by
    norm_num [gaussianMomentFormula, Real.Gamma_one_half_eq, ← Real.sqrt_eq_rpow]
  rw [he]
  apply (le_div_iff₀ (Real.sqrt_pos.2 Real.pi_pos)).2
  linarith

end
end LowRank
