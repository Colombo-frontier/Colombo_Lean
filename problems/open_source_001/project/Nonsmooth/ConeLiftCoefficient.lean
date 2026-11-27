import Nonsmooth.SubspaceConeLift

set_option autoImplicit false
namespace Nonsmooth
noncomputable section

def coneLiftCoefficient (ε : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => Real.sqrt ((coneLiftCoefficient ε n) ^ 2 + ((1 + coneLiftCoefficient ε n) * ε) ^ 2)

theorem coneLiftCoefficient_nonneg (ε : ℝ) (n : ℕ) : 0 ≤ coneLiftCoefficient ε n := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact Real.sqrt_nonneg _

theorem coneLiftCoefficient_step_sq (ε : ℝ) (n : ℕ) :
    (coneLiftCoefficient ε (n + 1)) ^ 2 =
      (coneLiftCoefficient ε n) ^ 2 + ((1 + coneLiftCoefficient ε n) * ε) ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem coneLiftCoefficient_sq_le {ε : ℝ} (hε : 0 ≤ ε) {D : ℕ}
    (hsmall : 4 * (D : ℝ) * ε ^ 2 ≤ 1) (n : ℕ) (hn : n ≤ D) :
    (coneLiftCoefficient ε n) ^ 2 ≤ 4 * (n : ℝ) * ε ^ 2 := by
  induction n with
  | zero => simp [coneLiftCoefficient]
  | succ n ih =>
    have hnD : n ≤ D := by omega
    have hi := ih hnD
    have hcast : (n : ℝ) ≤ D := by exact_mod_cast hnD
    have hnsmall : 4 * (n : ℝ) * ε ^ 2 ≤ 1 :=
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcast (by norm_num))
        (sq_nonneg ε)).trans hsmall
    have hc0 := coneLiftCoefficient_nonneg ε n
    have hc1 : coneLiftCoefficient ε n ≤ 1 := by nlinarith
    have hprod : (1 + coneLiftCoefficient ε n) * ε ≤ 2 * ε :=
      mul_le_mul_of_nonneg_right (by linarith) hε
    have hprod0 : 0 ≤ (1 + coneLiftCoefficient ε n) * ε :=
      mul_nonneg (by linarith) hε
    have hs : ((1 + coneLiftCoefficient ε n) * ε) ^ 2 ≤ 4 * ε ^ 2 := by
      nlinarith only [hprod, hprod0, hε]
    rw [coneLiftCoefficient_step_sq]
    push_cast
    nlinarith only [hi, hs]

theorem coneLiftCoefficient_dimension_scale (D : ℕ) (hD : 0 < D) (n : ℕ) (hn : n ≤ D) :
    coneLiftCoefficient (1 / (8 * (D : ℝ) ^ 2)) n ≤ 1 / (4 * (D : ℝ)) := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  let ε : ℝ := 1 / (8 * (D : ℝ) ^ 2)
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hscale : 4 * (D : ℝ) * ε ^ 2 ≤ (1 / (4 * (D : ℝ))) ^ 2 := by
    have heq : 4 * (D : ℝ) * ε ^ 2 = 1 / (16 * (D : ℝ) ^ 3) := by
      dsimp [ε]
      field_simp
      ring
    rw [heq, div_pow, one_pow]
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 16 * (D : ℝ) ^ 3)
      (by positivity : (0 : ℝ) < (4 * (D : ℝ)) ^ 2)).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hD1) (sq_nonneg (D : ℝ))]
  have hunit : (1 / (4 * (D : ℝ))) ^ 2 ≤ 1 := by
    have hp : 0 ≤ 1 / (4 * (D : ℝ)) := by positivity
    have hq : 1 / (4 * (D : ℝ)) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    nlinarith
  have hc := coneLiftCoefficient_sq_le hε (hscale.trans hunit) n hn
  have hcast : (n : ℝ) ≤ D := by exact_mod_cast hn
  have hnd := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcast (by norm_num : (0 : ℝ) ≤ 4))
    (sq_nonneg ε)
  have hbound := (hc.trans hnd).trans hscale
  have hr : 0 ≤ 1 / (4 * (D : ℝ)) := by positivity
  change coneLiftCoefficient ε n ≤ _
  nlinarith only [hbound, hr]

end
end Nonsmooth
