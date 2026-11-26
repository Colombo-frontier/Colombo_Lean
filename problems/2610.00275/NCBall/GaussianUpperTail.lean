import NCBall.GaussianSmallBall

/-! # Positive Gaussian square moments and the good-event tail -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal
namespace NCBall

theorem gaussian_square_mgf {v : ℝ≥0} (hv : 0 < v) :
    (∫ x : ℝ, Real.exp (x ^ 2 / (4 * (v : ℝ))) ∂gaussianReal 0 v) = Real.sqrt 2 := by
  have hv' : (0 : ℝ) < v := by exact_mod_cast hv
  rw [integral_gaussianReal_eq_integral_smul (ne_of_gt hv)]
  have he (x : ℝ) : gaussianPDFReal 0 v x • Real.exp (x ^ 2 / (4 * (v : ℝ))) =
      (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ * Real.exp (-(1 / (4 * (v : ℝ))) * x ^ 2) := by
    simp only [gaussianPDFReal, sub_zero, smul_eq_mul, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  simp_rw [he]
  rw [integral_const_mul, integral_gaussian]
  calc
    _ = Real.sqrt (Real.pi / (1 / (4 * (v : ℝ)))) / Real.sqrt (2 * Real.pi * (v : ℝ)) := by ring
    _ = Real.sqrt ((Real.pi / (1 / (4 * (v : ℝ)))) / (2 * Real.pi * (v : ℝ))) :=
      (Real.sqrt_div (by positivity) _).symm
    _ = Real.sqrt 2 := by
      congr 1
      field_simp
      ring

theorem gaussian_square_mgf_integrable {v : ℝ≥0} (hv : 0 < v) :
    Integrable (fun x : ℝ => Real.exp (x ^ 2 / (4 * (v : ℝ)))) (gaussianReal 0 v) := by
  by_contra h
  have hi := gaussian_square_mgf hv
  rw [integral_undef h] at hi
  have : 0 < Real.sqrt (2 : ℝ) := by positivity
  linarith

def isotropicGaussian (n : ℕ) : Measure (Fin n → ℝ) :=
  diagonalGaussian (fun _ => 0) (fun _ => ⟨1 / n, by positivity⟩)

instance (n : ℕ) : IsProbabilityMeasure (isotropicGaussian n) := by
  unfold isotropicGaussian
  infer_instance

def coordinateNormSq {n : ℕ} (x : Fin n → ℝ) : ℝ := ∑ i, (x i) ^ 2

theorem coordinateNormSq_nonneg {n : ℕ} (x : Fin n → ℝ) : 0 ≤ coordinateNormSq x := by
  exact Finset.sum_nonneg (fun i _ => sq_nonneg (x i))

theorem isotropicGaussian_exp_integral {n : ℕ} (hn : 0 < n) :
    (∫ x, Real.exp ((n : ℝ) / 4 * coordinateNormSq x) ∂isotropicGaussian n) =
      Real.sqrt 2 ^ n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hfactor (z : ℝ) : (n : ℝ) / 4 * z ^ 2 = z ^ 2 / (4 * (1 / (n : ℝ))) := by
    field_simp
    ring
  have he (x : Fin n → ℝ) : Real.exp ((n : ℝ) / 4 * coordinateNormSq x) =
      ∏ i, Real.exp ((n : ℝ) / 4 * (x i) ^ 2) := by
    rw [coordinateNormSq, Finset.mul_sum, Real.exp_sum]
  simp_rw [he]
  rw [isotropicGaussian, diagonalGaussian_integral_prod (fun _ : Fin n => 0)
    (fun _ => ⟨1 / n, by positivity⟩) (fun _ z => Real.exp ((n : ℝ) / 4 * z ^ 2))]
  simp_rw [hfactor]
  have hm : (∫ z : ℝ, Real.exp (z ^ 2 / (4 * (1 / (n : ℝ))))
      ∂gaussianReal 0 ⟨1 / (n : ℝ), by positivity⟩) = Real.sqrt 2 :=
    gaussian_square_mgf (show (0 : ℝ) < 1 / (n : ℝ) by positivity)
  simp only [hm, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem isotropicGaussian_exp_integrable {n : ℕ} (hn : 0 < n) :
    Integrable (fun x => Real.exp ((n : ℝ) / 4 * coordinateNormSq x)) (isotropicGaussian n) := by
  by_contra h
  have hi := isotropicGaussian_exp_integral hn
  rw [integral_undef h] at hi
  have : 0 < Real.sqrt (2 : ℝ) ^ n := by positivity
  linarith

theorem isotropicGaussian_exp_bound {n : ℕ} (hn : 0 < n) :
    (∫ x, Real.exp ((n : ℝ) / 4 * coordinateNormSq x) ∂isotropicGaussian n) ≤
      Real.exp ((n : ℝ) / 2) := by
  rw [isotropicGaussian_exp_integral hn]
  have h : Real.sqrt 2 ≤ Real.exp (1 / 2) := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have he := Real.add_one_le_exp (1 / 2)
    have hp : 0 ≤ Real.sqrt (2 : ℝ) := Real.sqrt_nonneg _
    nlinarith
  calc
    _ ≤ Real.exp (1 / 2) ^ n := pow_le_pow_left₀ (Real.sqrt_nonneg _) h n
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

/-- A norm larger than 2 has probability at most exp(-n/2). -/
theorem isotropicGaussian_norm_tail {n : ℕ} (hn : 0 < n) :
    (isotropicGaussian n).real {x | 4 < coordinateNormSq x} ≤ Real.exp (-(n : ℝ) / 2) := by
  let μ := isotropicGaussian n
  let f := fun x : Fin n → ℝ => Real.exp ((n : ℝ) / 4 * coordinateNormSq x)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsub : {x : Fin n → ℝ | 4 < coordinateNormSq x} ⊆ {x | Real.exp n ≤ f x} := by
    intro x hx
    apply Real.exp_le_exp.mpr
    dsimp [f]
    dsimp at hx
    nlinarith
  have hm := mul_meas_ge_le_integral_of_nonneg (μ := μ) (f := f)
    (ae_of_all _ (fun _ => (Real.exp_pos _).le)) (isotropicGaussian_exp_integrable hn) (Real.exp n)
  have hmono := mul_le_mul_of_nonneg_left (measureReal_mono (μ := μ) hsub) (Real.exp_pos (n : ℝ)).le
  have hb := hmono.trans (hm.trans (isotropicGaussian_exp_bound hn))
  calc
    _ ≤ Real.exp ((n : ℝ) / 2) / Real.exp n :=
      (le_div_iff₀ (Real.exp_pos _)).2 (by simpa only [mul_comm] using hb)
    _ = Real.exp (-(n : ℝ) / 2) := by rw [← Real.exp_sub]; congr 1; ring

end NCBall
