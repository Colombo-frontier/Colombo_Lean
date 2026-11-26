import NCBall.GaussianLaplace
import Mathlib.MeasureTheory.Integral.Pi

/-!
# An exponential small-ball bound for independent Gaussian coordinates

This proves the analytic small-ball step uniformly over translations. It uses
negative exponential moments instead of Anderson's inequality. Connecting these
independent coordinates to the eigenbasis of an adaptive posterior is separate.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal
namespace NCBall

def diagonalGaussian {k : ℕ} (m : Fin k → ℝ) (v : Fin k → ℝ≥0) :
    Measure (Fin k → ℝ) := Measure.pi (fun i => gaussianReal (m i) (v i))

instance {k : ℕ} (m : Fin k → ℝ) (v : Fin k → ℝ≥0) :
    IsProbabilityMeasure (diagonalGaussian m v) := by unfold diagonalGaussian; infer_instance

theorem diagonalGaussian_integral_prod {k : ℕ} (m : Fin k → ℝ) (v : Fin k → ℝ≥0)
    (f : Fin k → ℝ → ℝ) :
    (∫ x, ∏ i, f i (x i) ∂diagonalGaussian m v) =
      ∏ i, ∫ x, f i x ∂gaussianReal (m i) (v i) := by
  let inst : (i : Fin k) → MeasureSpace ℝ := fun i => ⟨gaussianReal (m i) (v i)⟩
  have h := @integral_fintype_prod_eq_prod ℝ _ (Fin k) _ (fun _ => ℝ) f inst
    (fun i => (inferInstance : SigmaFinite (gaussianReal (m i) (v i))))
  exact h

theorem diagonalGaussian_integrable_prod {k : ℕ} (m : Fin k → ℝ) (v : Fin k → ℝ≥0)
    (f : Fin k → ℝ → ℝ) (hf : ∀ i, Integrable (f i) (gaussianReal (m i) (v i))) :
    Integrable (fun x => ∏ i, f i (x i)) (diagonalGaussian m v) := by
  let inst : (i : Fin k) → MeasureSpace ℝ := fun i => ⟨gaussianReal (m i) (v i)⟩
  exact @Integrable.fintype_prod_dep ℝ _ (Fin k) _ (fun _ => ℝ) f inst
    (fun i => (inferInstance : SigmaFinite (gaussianReal (m i) (v i)))) hf

theorem exp_neg_sum_sq_eq_prod {k : ℕ} (a : ℝ) (u x : Fin k → ℝ) :
    Real.exp (-a * ∑ i, (x i - u i) ^ 2) =
      ∏ i, Real.exp (-a * (x i - u i) ^ 2) := by
  rw [Finset.mul_sum, Real.exp_sum]

theorem diagonalGaussian_laplace_bound {k : ℕ} (m u : Fin k → ℝ) (v : Fin k → ℝ≥0)
    {a : ℝ} (ha : 0 < a) (hv : ∀ i, 1 / (2 * a) ≤ (v i : ℝ)) :
    (∫ x, Real.exp (-a * ∑ i, (x i - u i) ^ 2) ∂diagonalGaussian m v) ≤
      Real.exp (-(k : ℝ) / 4) := by
  let t : ℝ≥0 := ⟨1 / (2 * a), by positivity⟩
  have ht : 0 < t := (show (0 : ℝ) < 1 / (2 * a) by positivity)
  have heq (i : Fin k) (z : ℝ) : Real.exp (-a * (z - u i) ^ 2) =
      Real.exp (-(z - u i) ^ 2 / (2 * (t : ℝ))) := by
    congr 1
    dsimp [t]
    field_simp
    ring
  have hfactor (i : Fin k) :
      (∫ z, Real.exp (-a * (z - u i) ^ 2) ∂gaussianReal (m i) (v i)) ≤ 3 / 4 := by
    simp_rw [heq]
    exact gaussianLaplace_le_three_quarters (m i) (u i) ht (hv i)
  simp_rw [exp_neg_sum_sq_eq_prod]
  rw [diagonalGaussian_integral_prod m v (fun i z => Real.exp (-a * (z - u i) ^ 2))]
  calc
    _ ≤ ∏ _i : Fin k, (3 / 4 : ℝ) :=
      Finset.prod_le_prod (fun i _ => integral_nonneg (fun _ => (Real.exp_pos _).le))
        (fun i _ => hfactor i)
    _ = (3 / 4 : ℝ) ^ k := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ Real.exp (-1 / 4) ^ k := by
      apply pow_le_pow_left₀ (by norm_num)
      have h := Real.add_one_le_exp (-1 / 4)
      linarith
    _ = Real.exp (-(k : ℝ) / 4) := by rw [← Real.exp_nat_mul]; congr 1; ring

/-- The radius 1/16 bound with explicit exponent 1/8.
The hypotheses require at least 3a/4 independent coordinates, each with
variance at least 1/(2a). Lemma 8.2 gives the stronger variance 4/(5a). -/
theorem diagonalGaussian_smallBall {k : ℕ} (m u : Fin k → ℝ) (v : Fin k → ℝ≥0)
    {a : ℝ} (ha : 0 < a) (hk : 3 * a / 4 ≤ (k : ℝ))
    (hv : ∀ i, 1 / (2 * a) ≤ (v i : ℝ)) :
    (diagonalGaussian m v).real {x | ∑ i, (x i - u i) ^ 2 ≤ 1 / 256} ≤
      Real.exp (-a / 8) := by
  let μ := diagonalGaussian m v
  let f := fun x : Fin k → ℝ => Real.exp (-a * ∑ i, (x i - u i) ^ 2)
  have hf : Integrable f μ := by
    have hi (i : Fin k) : Integrable (fun z : ℝ => Real.exp (-a * (z - u i) ^ 2))
        (gaussianReal (m i) (v i)) := by
      have hc : Continuous (fun z : ℝ => Real.exp (-a * (z - u i) ^ 2)) := by fun_prop
      apply (integrable_const (1 : ℝ)).mono' hc.aestronglyMeasurable
      filter_upwards [] with z
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_one_iff.mpr
      nlinarith [sq_nonneg (z - u i)]
    simpa only [f, exp_neg_sum_sq_eq_prod] using
      diagonalGaussian_integrable_prod m v (fun i z => Real.exp (-a * (z - u i) ^ 2)) hi
  have hcontain : {x : Fin k → ℝ | ∑ i, (x i - u i) ^ 2 ≤ 1 / 256} ⊆
      {x | Real.exp (-a / 256) ≤ f x} := by
    intro x hx
    apply Real.exp_le_exp.mpr
    dsimp [f]
    dsimp at hx
    nlinarith
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (f := f) (ae_of_all _ (fun _ => (Real.exp_pos _).le)) hf (Real.exp (-a / 256))
  have hmono := mul_le_mul_of_nonneg_left (measureReal_mono (μ := μ) hcontain)
    (Real.exp_pos (-a / 256)).le
  have hbound := diagonalGaussian_laplace_bound m u v ha hv
  have hmul : Real.exp (-a / 256) * μ.real {x | ∑ i, (x i - u i) ^ 2 ≤ 1 / 256} ≤
      Real.exp (-(k : ℝ) / 4) := hmono.trans (hmarkov.trans hbound)
  calc
    _ ≤ Real.exp (-(k : ℝ) / 4) / Real.exp (-a / 256) :=
      (le_div_iff₀ (Real.exp_pos _)).2 (by simpa only [mul_comm] using hmul)
    _ = Real.exp (-(k : ℝ) / 4 - (-a / 256)) := (Real.exp_sub _ _).symm
    _ ≤ Real.exp (-a / 8) := Real.exp_le_exp.mpr (by linarith)

end NCBall
