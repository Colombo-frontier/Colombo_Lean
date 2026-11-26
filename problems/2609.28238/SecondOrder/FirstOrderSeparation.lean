import SecondOrder.FirstOrderRegularizer

open scoped BigOperators Classical

namespace SecondOrder
noncomputable section
variable {d : ℕ}

def firstOrderGradientConstant : ℝ := 4*(Real.sqrt 2-1-1/4)
def firstOrderGradientPolynomial (c r : ℝ) : ℝ := 2*c*r^2+8*r-2*c

theorem firstOrderGradientConstant_pos : 0<firstOrderGradientConstant := by
  have hs := Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
  have hn := Real.sqrt_nonneg 2
  unfold firstOrderGradientConstant
  nlinarith

/-- A one-sided root estimate suffices for the mean-correlation obstruction;
it retains the manuscript's exact positive constant. -/
theorem firstOrderGradientPolynomial_lower {c r : ℝ} (hc : 2≤c) (hr : -1≤r ∧ r≤1) :
    4*(Real.sqrt 2-1-r)≤|firstOrderGradientPolynomial c r| := by
  have hs := Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
  have hroot : (Real.sqrt 2-1)^2+2*(Real.sqrt 2-1)-1=0 := by nlinarith only [hs]
  have hpos : 0≤Real.sqrt 2-1 := by nlinarith [Real.sqrt_nonneg 2]
  by_cases hh : r≤Real.sqrt 2-1
  · have hprod := mul_nonneg (sub_nonneg.mpr hh) (show 0≤r+(Real.sqrt 2-1)+1 by linarith only [hr.1,hpos])
    have hr2 : r^2≤1 := by nlinarith [mul_nonneg (by linarith only [hr.1] : 0≤r+1) (by linarith only [hr.2] : 0≤1-r)]
    have hcprod := mul_nonneg (sub_nonneg.mpr hc) (sub_nonneg.mpr hr2)
    have hz := neg_le_abs (firstOrderGradientPolynomial c r)
    unfold firstOrderGradientPolynomial at hz ⊢
    nlinarith only [hroot,hprod,hcprod,hz]
  · exact (show 4*(Real.sqrt 2-1-r)≤0 by linarith only [hh]).trans (abs_nonneg _)

theorem euclidean_abs_sum_le (v : Point d) : (∑ i, |v i|)≤Real.sqrt d*‖v‖ := by
  have hh := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : Fin d => (1:ℝ)) (fun i => |v i|)
  simp only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,sq_abs] at hh
  rw [←euclidean_norm_sq] at hh
  have hs := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) d)
  have hn : 0≤Real.sqrt d*‖v‖ := by positivity
  have he : (Real.sqrt d*‖v‖)^2=(d:ℝ)*‖v‖^2 := by rw [mul_pow,hs]
  nlinarith [Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => abs_nonneg (v i))]

theorem firstOrderGradientPolynomial_norm_lower (r : Fin d → ℝ) {c : ℝ} (hc : 2≤c)
    (hr : ∀ i, -1≤r i ∧ r i≤1) (havg : ∑ i, r i≤(d:ℝ)/4) :
    firstOrderGradientConstant*(d:ℝ)≤
      Real.sqrt d*‖euclideanVector (fun i => firstOrderGradientPolynomial c (r i))‖ := by
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => firstOrderGradientPolynomial_lower hc (hr i))
  have he : (∑ i : Fin d, 4*(Real.sqrt 2-1-r i))=
      4*((d:ℝ)*(Real.sqrt 2-1)-∑ i, r i) := by
    rw [←Finset.mul_sum,Finset.sum_sub_distrib]
    simp
    <;> ring
  rw [he] at hh
  have hn := euclidean_abs_sum_le (euclideanVector (fun i => firstOrderGradientPolynomial c (r i)))
  simp only [euclideanVector_apply] at hn
  unfold firstOrderGradientConstant
  nlinarith only [hh,hn,havg]

def firstOrderBlockForce (θ : Fin d → Bool) (B : ℝ) (x : Point d) : Point d :=
  euclideanVector (fun i => 2*B*signValue (θ i)*tanhFirst (Real.sqrt d*x i)+8*Real.tanh (Real.sqrt d*x i))

theorem firstOrderBlockForce_abs (θ : Fin d → Bool) (B : ℝ) (x : Point d) (i : Fin d) :
    |firstOrderBlockForce θ B x i|=
      |firstOrderGradientPolynomial (-B) (signValue (θ i)*Real.tanh (Real.sqrt d*x i))| := by
  have he : signValue (θ i)*firstOrderBlockForce θ B x i=
      firstOrderGradientPolynomial (-B) (signValue (θ i)*Real.tanh (Real.sqrt d*x i)) := by
    cases hi : θ i <;> simp [firstOrderBlockForce,euclideanVector_apply,hi,signValue,tanhFirst,firstOrderGradientPolynomial] <;> ring
  have hs : |signValue (θ i)|=1 := by cases hi : θ i <;> norm_num [hi,signValue]
  rw [←he,abs_mul,hs,one_mul]

theorem firstOrderBlockForce_norm (θ : Fin d → Bool) (B : ℝ) (x : Point d) :
    ‖firstOrderBlockForce θ B x‖=
      ‖euclideanVector (fun i => firstOrderGradientPolynomial (-B) (signValue (θ i)*Real.tanh (Real.sqrt d*x i)))‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  simp only [euclidean_norm_sq,euclideanVector_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [←sq_abs (firstOrderBlockForce θ B x i),firstOrderBlockForce_abs,sq_abs]

theorem firstOrderBlockForce_lower (θ : Fin d → Bool) {B : ℝ} (hB : B≤-2) (hd : 0<d)
    (x : Point d) (hx : firstOrderBlockEncoding θ x≤1/2) :
    firstOrderGradientConstant*(d:ℝ)≤Real.sqrt d*‖firstOrderBlockForce θ B x‖ := by
  rw [firstOrderBlockForce_norm]
  apply firstOrderGradientPolynomial_norm_lower _ (by linarith only [hB])
  · intro i
    have ht := tanh_abs_le_one (Real.sqrt d*x i)
    apply abs_le.mp
    rw [abs_mul]
    have hs : |signValue (θ i)|=1 := by cases hi : θ i <;> norm_num [hi,signValue]
    rwa [hs,one_mul]
  · have hD : (0:ℝ)<d := by exact_mod_cast hd
    rw [firstOrderBlockEncoding_eq] at hx
    unfold firstOrderEncoding rademacherSum at hx
    have he : (2/(d:ℝ))*(∑ i, signValue (θ i)*Real.tanh (Real.sqrt d*x i))≤1/2 := by
      simpa only [mul_comm] using hx
    have hh := mul_le_mul_of_nonneg_left he hD.le
    field_simp [hD.ne'] at hh
    linarith only [hh]

end
end SecondOrder
