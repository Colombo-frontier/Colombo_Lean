import GaussianOCO254
import IntervalRestart254

noncomputable section
namespace Paper254

theorem good_history_budget (a B lam L z : ℝ) (ha : 0 ≤ a) (hB : 0 ≤ B)
    (hlam : 0 < lam) (hL : 1 ≤ L) (hz : 0 ≤ z)
    (hsmall : z ≤ Real.sqrt (B+lam*(128*L*(a+B/lam)))/(512*L)) :
    a+(Real.sqrt (B+lam*(128*L*(a+B/lam)))+z)^2/lam-128*L*(a+B/lam) ≤
      (128*L*(a+B/lam))/(64*L) := by
  let A := a+B/lam
  let H := 128*L*A
  let C := B+lam*H
  let e := 1/(512*L)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hLp : 0 < L := by linarith
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hroot := Real.sqrt_nonneg C
  have hroot2 := Real.sq_sqrt hC
  have hzbound : z ≤ Real.sqrt C*e := by simpa [C, H, A, e, div_eq_mul_inv] using hsmall
  have hs : (Real.sqrt C+z)^2 ≤ C*(1+e)^2 := by
    have hm := mul_nonneg (sub_nonneg.mpr hzbound) (add_nonneg
      (add_nonneg (mul_nonneg hroot he) hz) (by linarith : 0 ≤ 2*Real.sqrt C))
    nlinarith
  have hdiv := div_le_div_of_nonneg_right hs hlam.le
  have hc : C/lam ≤ (1+128*L)*A := by
    dsimp [C, H, A]
    field_simp
    nlinarith
  have hcoef : (2*e+e^2)*(1+128*L) ≤ 1 := by
    convert Audit254.good_node_coefficient L hL using 1 <;> dsimp [e] <;> ring
  have hec : 0 ≤ 2*e+e^2 := by positivity
  have hc1 := mul_le_mul_of_nonneg_left hc hec
  have hc2 := mul_le_mul_of_nonneg_right hcoef hA
  have hcost : (2*e+e^2)*(C/lam) ≤ A := by nlinarith
  have hbase : a+C/lam-H = A := by
    dsimp [C, H, A]
    field_simp
    ring
  have htarget : H/(64*L) = 2*A := by dsimp [H]; field_simp; ring
  change a+(Real.sqrt C+z)^2/lam-H ≤ H/(64*L)
  rw [htarget]
  have heq : C*(1+e)^2/lam = C/lam+(2*e+e^2)*(C/lam) := by ring
  rw [heq] at hdiv
  linarith

theorem variation_threshold_movement (q C L P : ℝ) (hq : 0 < q) (hC : 0 ≤ C)
    (hL : 0 < L) (hP : 0 ≤ P) (hsmall : P ≤ Real.sqrt q*Real.sqrt C/(512*L)) :
    P/(Real.sqrt 2*Real.sqrt q) ≤ Real.sqrt C/(512*L) := by
  have hs2 : 1 ≤ Real.sqrt 2 := by
    have hh := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith [Real.sqrt_nonneg 2]
  have hqroot : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  have hbase : P/Real.sqrt q ≤ Real.sqrt C/(512*L) := by
    apply (div_le_iff₀ hqroot).mpr
    convert hsmall using 1 <;> ring
  have hden : Real.sqrt q ≤ Real.sqrt 2*Real.sqrt q := by nlinarith
  exact le_trans (div_le_div_of_nonneg_left hP hqroot hden) hbase

end Paper254
#print axioms Paper254.good_history_budget
#print axioms Paper254.variation_threshold_movement
