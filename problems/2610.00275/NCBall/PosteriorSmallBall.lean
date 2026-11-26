import NCBall.GaussianSmallBall
import NCBall.Information

/-!
# Full spectral small-ball calculation for a diagonal posterior

The only missing step to apply this to the paper's adaptive experiment is to
prove that its conditional law, in a measurable eigenbasis, is this Gaussian.
Neither a covariance formula nor a conditional-law identity is assumed silently.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal
namespace NCBall

theorem laplace_smallBall_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (energy : Ω → ℝ) {a K : ℝ}
    (ha : 0 < a) (hK : 3 * a / 4 ≤ K)
    (hf : Integrable (fun x => Real.exp (-a * energy x)) μ)
    (hint : ∫ x, Real.exp (-a * energy x) ∂μ ≤ Real.exp (-K / 4)) :
    μ.real {x | energy x ≤ 1 / 256} ≤ Real.exp (-a / 8) := by
  have hs : {x | energy x ≤ 1 / 256} ⊆
      {x | Real.exp (-a / 256) ≤ Real.exp (-a * energy x)} := by
    intro x hx
    apply Real.exp_le_exp.mpr
    dsimp at hx
    nlinarith
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (f := fun x => Real.exp (-a * energy x))
    (ae_of_all _ (fun _ => (Real.exp_pos _).le)) hf (Real.exp (-a / 256))
  have hmono := mul_le_mul_of_nonneg_left (measureReal_mono (μ := μ) hs)
    (Real.exp_pos (-a / 256)).le
  calc
    _ ≤ Real.exp (-K / 4) / Real.exp (-a / 256) :=
      (le_div_iff₀ (Real.exp_pos _)).2
        (by simpa only [mul_comm] using hmono.trans (hmarkov.trans hint))
    _ = Real.exp (-K / 4 - (-a / 256)) := (Real.exp_sub _ _).symm
    _ ≤ Real.exp (-a / 8) := Real.exp_le_exp.mpr (by linarith)

theorem diagonalGaussian_laplace_on {k : ℕ} (m u : Fin k → ℝ) (v : Fin k → ℝ≥0)
    (S : Finset (Fin k)) {a : ℝ} (ha : 0 < a)
    (hv : ∀ i ∈ S, 1 / (2 * a) ≤ (v i : ℝ)) :
    (∫ x, Real.exp (-a * ∑ i, (x i - u i) ^ 2) ∂diagonalGaussian m v) ≤
      Real.exp (-(S.card : ℝ) / 4) := by
  let t : ℝ≥0 := ⟨1 / (2 * a), by positivity⟩
  have ht : 0 < t := (show (0 : ℝ) < 1 / (2 * a) by positivity)
  have heq (i : Fin k) (z : ℝ) : Real.exp (-a * (z - u i) ^ 2) =
      Real.exp (-(z - u i) ^ 2 / (2 * (t : ℝ))) := by
    congr 1
    dsimp [t]
    field_simp
    ring
  have hfactor (i : Fin k) :
      (∫ z, Real.exp (-a * (z - u i) ^ 2) ∂gaussianReal (m i) (v i)) ≤
      if i ∈ S then 3 / 4 else 1 := by
    split_ifs with hi
    · simp_rw [heq]
      exact gaussianLaplace_le_three_quarters (m i) (u i) ht (hv i hi)
    · have hint : Integrable (fun z => Real.exp (-a * (z - u i) ^ 2))
          (gaussianReal (m i) (v i)) := by
        simp_rw [heq]
        exact gaussianLaplace_integrable (m i) (u i) (v i) t
      have hh : ∫ z, Real.exp (-a * (z - u i) ^ 2) ∂gaussianReal (m i) (v i) ≤
          ∫ _z, (1 : ℝ) ∂gaussianReal (m i) (v i) := by
        apply integral_mono hint (integrable_const _)
        intro z
        apply Real.exp_le_one_iff.mpr
        nlinarith [sq_nonneg (z - u i)]
      simpa using hh
  simp_rw [exp_neg_sum_sq_eq_prod]
  rw [diagonalGaussian_integral_prod m v (fun i z => Real.exp (-a * (z - u i) ^ 2))]
  calc
    _ ≤ ∏ i : Fin k, (if i ∈ S then (3 / 4 : ℝ) else 1) :=
      Finset.prod_le_prod (fun i _ => integral_nonneg (fun _ => (Real.exp_pos _).le))
        (fun i _ => hfactor i)
    _ = (3 / 4 : ℝ) ^ S.card := by rw [Fintype.prod_ite_mem]; simp only [Finset.prod_const]
    _ ≤ Real.exp (-1 / 4) ^ S.card := by
      apply pow_le_pow_left₀ (by norm_num)
      have h := Real.add_one_le_exp (-1 / 4)
      linarith
    _ = Real.exp (-(S.card : ℝ) / 4) := by rw [← Real.exp_nat_mul]; congr 1; ring

theorem diagonalGaussian_smallBall_on {k : ℕ} (m u : Fin k → ℝ) (v : Fin k → ℝ≥0)
    (S : Finset (Fin k)) {a : ℝ} (ha : 0 < a) (hS : 3 * a / 4 ≤ (S.card : ℝ))
    (hv : ∀ i ∈ S, 1 / (2 * a) ≤ (v i : ℝ)) :
    (diagonalGaussian m v).real {x | ∑ i, (x i - u i) ^ 2 ≤ 1 / 256} ≤
      Real.exp (-a / 8) := by
  apply laplace_smallBall_bound (diagonalGaussian m v) (fun x => ∑ i, (x i - u i) ^ 2)
    ha hS
  · have hc : Continuous (fun x : Fin k → ℝ => Real.exp (-a * ∑ i, (x i - u i) ^ 2)) := by
      fun_prop
    apply (integrable_const (1 : ℝ)).mono' hc.aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_one_iff.mpr
    have hs : 0 ≤ ∑ i, (x i - u i) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    nlinarith
  · exact diagonalGaussian_laplace_on m u v S ha hv

/-- Analytic content of (8.5), for the diagonal Gaussian with the eigenvalues
dictated by (8.2). The mean and the proposed estimator are entirely arbitrary. -/
theorem posterior_diagonal_smallBall {n : ℕ} (hn : 0 < n) (a m u : Fin n → ℝ)
    {σ2 : ℝ} (hσ : 0 < σ2) (ha : ∀ i, 0 ≤ a i)
    (htrace : ∑ i, a i < n * σ2 / 16) :
    let v : Fin n → ℝ≥0 := fun i => ⟨1 / ((n : ℝ) * (1 + a i / σ2)), by
      have hai := ha i
      positivity⟩
    (diagonalGaussian m v).real {x | ∑ i, (x i - u i) ^ 2 ≤ 1 / 256} ≤
      Real.exp (-(n : ℝ) / 8) := by
  dsimp only
  classical
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  apply diagonalGaussian_smallBall_on m u _ (Finset.univ.filter (fun i => a i ≤ σ2 / 4))
    hn' (many_small_eigenvalues a hσ ha htrace)
  intro i hi
  have hl := posterior_variance_lower hn' hσ (ha i) (Finset.mem_filter.mp hi).2
  have hcompare : 1 / (2 * (n : ℝ)) ≤ 4 / (5 * (n : ℝ)) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    linarith
  exact hcompare.trans hl

end NCBall
