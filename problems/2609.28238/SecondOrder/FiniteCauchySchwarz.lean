import SecondOrder.FiniteMean

open scoped BigOperators

namespace SecondOrder
noncomputable section
variable {α : Type*} [Fintype α]

/-- Weighted Cauchy–Schwarz for any finite PMF, including zero masses. -/
theorem pmfMean_mul_sq_le (p : PMF α) (X Y : α → ℝ) :
    (pmfMean p (fun a => X a*Y a))^2 ≤ pmfMean p (fun a => X a^2)*pmfMean p (fun a => Y a^2) := by
  have hw (a : α) : (Real.sqrt (p a).toReal)^2 = (p a).toReal := Real.sq_sqrt ENNReal.toReal_nonneg
  have hx (a : α) : (Real.sqrt (p a).toReal*X a)^2 = (p a).toReal*X a^2 := by rw [mul_pow, hw]
  have hy (a : α) : (Real.sqrt (p a).toReal*Y a)^2 = (p a).toReal*Y a^2 := by rw [mul_pow, hw]
  have hxy (a : α) : (Real.sqrt (p a).toReal*X a)*(Real.sqrt (p a).toReal*Y a) = (p a).toReal*(X a*Y a) := by
    calc
      _ = (Real.sqrt (p a).toReal)^2*(X a*Y a) := by ring
      _ = _ := by rw [hw]
  have hh := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun a => Real.sqrt (p a).toReal*X a) (fun a => Real.sqrt (p a).toReal*Y a)
  simpa only [hx, hy, hxy, pmfMean, smul_eq_mul] using hh

theorem pmfMean_abs_mul_le (p : PMF α) (X Y : α → ℝ) :
    pmfMean p (fun a => |X a*Y a|) ≤
      Real.sqrt (pmfMean p (fun a => X a^2))*Real.sqrt (pmfMean p (fun a => Y a^2)) := by
  have hh := pmfMean_mul_sq_le p (fun a => |X a|) (fun a => |Y a|)
  simp only [← abs_mul, sq_abs] at hh
  have hr := Real.le_sqrt_of_sq_le hh
  rw [Real.sqrt_mul (pmfMean_nonneg p (fun a => sq_nonneg (X a)))] at hr
  exact hr

theorem pmfMean_abs_le_sqrt (p : PMF α) (X : α → ℝ) :
    pmfMean p (fun a => |X a|) ≤ Real.sqrt (pmfMean p (fun a => X a^2)) := by
  have hh := pmfMean_abs_mul_le p X (fun _ => 1)
  simpa only [mul_one, one_pow, pmfMean_const, Real.sqrt_one] using hh

end
end SecondOrder
