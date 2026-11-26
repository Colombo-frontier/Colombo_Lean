import DeterminantPerturbation254
import GaussianAlgebra254

noncomputable section
open scoped BigOperators Matrix
open Matrix
namespace Paper254

theorem quadratic_entry_perturbation {d : ℕ} (A B : Precision d) (x y : Coordinates d)
    (M R e t : ℝ) (hM : 0≤M) (hR : 0≤R) (he : 0≤e) (ht : 0≤t)
    (hB : ∀ i j,|B i j|≤M) (hAB : ∀ i j,|A i j-B i j|≤e)
    (hx : ∀ i,|x i|≤R) (hy : ∀ i,|y i|≤R) (hxy : ∀ i,|x i-y i|≤t) :
    |matrixQuadratic A x-matrixQuadratic B y|≤(d:ℝ)^2*(e*R^2+2*M*R*t) := by
  have hexpand : matrixQuadratic A x-matrixQuadratic B y=
      ∑ i,∑ j,(x i*A i j*x j-y i*B i j*y j) := by
    simp only [matrixQuadratic,dotProduct,Matrix.mulVec,Finset.mul_sum,Finset.sum_sub_distrib]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> apply Finset.sum_congr rfl <;> intro j _ <;> ring
  rw [hexpand]
  have hentry : ∀ i j,|x i*A i j*x j-y i*B i j*y j|≤e*R^2+2*M*R*t := by
    intro i j
    have hid : x i*A i j*x j-y i*B i j*y j=
        (A i j-B i j)*x i*x j+B i j*(x i-y i)*x j+B i j*y i*(x j-y j) := by ring
    rw [hid]
    calc
      _ ≤ (|(A i j-B i j)*x i*x j|+|B i j*(x i-y i)*x j|)+|B i j*y i*(x j-y j)| :=
        (abs_add_le _ _).trans (add_le_add_right (abs_add_le _ _) _)
      _ ≤ e*R*R+M*t*R+M*R*t := by
        simp only [abs_mul]
        gcongr <;> first | exact hAB _ _ | exact hx _ | exact hy _ | exact hxy _ | exact hB _ _
      _ = _ := by ring
  calc
    _ ≤ ∑ i,|∑ j,(x i*A i j*x j-y i*B i j*y j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i,∑ j,|x i*A i j*x j-y i*B i j*y j| :=
      Finset.sum_le_sum (fun _ _=>Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _i : Fin d,∑ _j : Fin d,(e*R^2+2*M*R*t) :=
      Finset.sum_le_sum (fun i _=>Finset.sum_le_sum (fun j _=>hentry i j))
    _ = _ := by simp; ring

theorem trace_entry_perturbation {d : ℕ} (A B : Precision d) (e : ℝ)
    (hAB : ∀ i j,|A i j-B i j|≤e) : |A.trace-B.trace|≤d*e := by
  rw [Matrix.trace,Matrix.trace,← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i,|A i i-B i i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d,e := Finset.sum_le_sum (fun i _=>hAB i i)
    _ = _ := by simp

theorem precision_potential_perturbation {d : ℕ} (P Q : PrecisionGaussian d)
    (q : ℝ) (hq : 0<q) (u : Coordinates d) (M R e t l : ℝ)
    (hM : 1≤M) (hR : 0≤R) (he : 0≤e) (ht : 0≤t) (hl : 0<l)
    (hdetP : l≤P.precision.det) (hdetQ : l≤Q.precision.det)
    (hP : ∀ i j,|P.precision i j|≤M) (hQ : ∀ i j,|Q.precision i j|≤M)
    (hPQ : ∀ i j,|P.precision i j-Q.precision i j|≤e)
    (huP : ∀ i,|u i-P.mean i|≤R) (huQ : ∀ i,|u i-Q.mean i|≤R)
    (hm : ∀ i,|P.mean i-Q.mean i|≤t) :
    |P.potential q u-Q.potential q u|≤
      (q*d*e+(Fintype.card (Equiv.Perm (Fin d)):ℝ)*d*e*M^d/l+
        (d:ℝ)^2*(e*R^2+2*M*R*t))/2 := by
  have htrace := trace_entry_perturbation P.precision Q.precision e hPQ
  have hlog := logdet_entry_perturbation P.precision Q.precision M e l hM he hl
    hdetP hdetQ hP hQ hPQ
  have hmean : ∀ i,|(u-P.mean) i-(u-Q.mean) i|≤t := by
    intro i
    change |(u i-P.mean i)-(u i-Q.mean i)|≤t
    rw [show (u i-P.mean i)-(u i-Q.mean i)=-(P.mean i-Q.mean i) by ring,abs_neg]
    exact hm i
  have hquad := quadratic_entry_perturbation P.precision Q.precision (u-P.mean) (u-Q.mean)
    M R e t (by linarith) hR he ht hQ hPQ huP huQ hmean
  have hid : P.potential q u-Q.potential q u=
      (q*(P.precision.trace-Q.precision.trace)-
        (Real.log P.precision.det-Real.log Q.precision.det)+
        (matrixQuadratic P.precision (u-P.mean)-matrixQuadratic Q.precision (u-Q.mean)))/2 := by
    unfold PrecisionGaussian.potential precisionCovariancePart
    rw [Real.log_mul (pow_ne_zero _ hq.ne') P.positive.det_pos.ne',
      Real.log_mul (pow_ne_zero _ hq.ne') Q.positive.det_pos.ne']
    ring
  rw [hid,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  calc
    _ ≤ |q*(P.precision.trace-Q.precision.trace)|+
        |Real.log P.precision.det-Real.log Q.precision.det|+
        |matrixQuadratic P.precision (u-P.mean)-matrixQuadratic Q.precision (u-Q.mean)| :=
      (abs_add_le _ _).trans (add_le_add_right
        (by simpa only [sub_zero,zero_sub,abs_neg] using
          (abs_sub_le (q*(P.precision.trace-Q.precision.trace)) 0
            (Real.log P.precision.det-Real.log Q.precision.det))) _)
    _ ≤ _ := by rw [abs_mul,abs_of_pos hq]; nlinarith [mul_le_mul_of_nonneg_left htrace hq.le]

end Paper254
#print axioms Paper254.precision_potential_perturbation
