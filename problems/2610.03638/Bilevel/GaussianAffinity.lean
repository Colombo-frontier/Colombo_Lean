import Bilevel.GaussianMoments
import Mathlib.MeasureTheory.Integral.Pi

/-! # Gaussian affinity

The geometric mean of the two opposite Gaussian densities is a scalar
multiple of the centered density. Its integral is calculated exactly.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Bilevel.GaussianAffinity

theorem geometric_mean (δ : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (x : ℝ) :
    Real.sqrt (gaussianPDFReal δ v x * gaussianPDFReal (-δ) v x) =
      Real.exp (-δ ^ 2 / (2 * (v : ℝ))) * gaussianPDFReal 0 v x := by
  have hvR : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  have hexp : -((x - δ) ^ 2) / (2 * (v : ℝ)) + -((x - -δ) ^ 2) / (2 * v) =
      2 * (-δ ^ 2 / (2 * v)) + 2 * (-x ^ 2 / (2 * v)) := by
    field_simp [hvR]
    ring
  unfold gaussianPDFReal
  rw [show (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ * Real.exp (-((x - δ) ^ 2) / (2 * v)) *
      ((Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ * Real.exp (-((x - -δ) ^ 2) / (2 * v))) =
      ((Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ *
        Real.exp (-δ ^ 2 / (2 * v)) * Real.exp (-x ^ 2 / (2 * v))) ^ 2 by
    rw [mul_pow, mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
    rw [mul_mul_mul_comm, ← Real.exp_add, hexp, Real.exp_add]
    norm_num
    ring]
  rw [Real.sqrt_sq (by positivity)]
  simp only [sub_zero]
  ring

theorem integrable_geometric_mean (δ : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    Integrable (fun x => Real.sqrt (gaussianPDFReal δ v x * gaussianPDFReal (-δ) v x)) := by
  simp_rw [geometric_mean δ v hv]
  exact (integrable_gaussianPDFReal 0 v).const_mul _

theorem affinity (δ : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    (∫ x : ℝ, Real.sqrt (gaussianPDFReal δ v x * gaussianPDFReal (-δ) v x)) =
      Real.exp (-δ ^ 2 / (2 * (v : ℝ))) := by
  simp_rw [geometric_mean δ v hv]
  rw [integral_const_mul, integral_gaussianPDFReal_eq_one 0 hv, mul_one]

def density (n : ℕ) (m : ℝ) (v : ℝ≥0) (x : Fin n → ℝ) : ℝ :=
  ∏ i, gaussianPDFReal m v (x i)

theorem density_nonnegative (n : ℕ) (m : ℝ) (v : ℝ≥0) (x : Fin n → ℝ) :
    0 ≤ density n m v x :=
  Finset.prod_nonneg (fun _ _ => gaussianPDFReal_nonneg _ _ _)

theorem density_integrable (n : ℕ) (m : ℝ) (v : ℝ≥0) : Integrable (density n m v) :=
  Integrable.fintype_prod (fun _ => integrable_gaussianPDFReal m v)

theorem density_integral (n : ℕ) (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    (∫ x, density n m v x) = 1 := by
  unfold density
  rw [integral_fintype_prod_eq_pow, integral_gaussianPDFReal_eq_one m hv]
  simp

theorem sqrt_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) :
    Real.sqrt (∏ i ∈ s, f i) = ∏ i ∈ s, Real.sqrt (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.prod_insert ha]
      rw [Real.sqrt_mul (hf a), ih]

theorem density_geometric_mean (n : ℕ) (δ : ℝ) (v : ℝ≥0) (x : Fin n → ℝ) :
    Real.sqrt (density n δ v x * density n (-δ) v x) =
      ∏ i, Real.sqrt (gaussianPDFReal δ v (x i) * gaussianPDFReal (-δ) v (x i)) := by
  rw [density, density, ← Finset.prod_mul_distrib]
  exact sqrt_prod Finset.univ _ (fun i =>
    mul_nonneg (gaussianPDFReal_nonneg _ _ _) (gaussianPDFReal_nonneg _ _ _))

theorem product_affinity (n : ℕ) (δ : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    (∫ x : Fin n → ℝ, Real.sqrt (density n δ v x * density n (-δ) v x)) =
      Real.exp (-(n : ℝ) * δ ^ 2 / (2 * (v : ℝ))) := by
  simp_rw [density_geometric_mean]
  rw [integral_fintype_prod_eq_pow (Fin n) (fun z : ℝ =>
    Real.sqrt (gaussianPDFReal δ v z * gaussianPDFReal (-δ) v z)),
    affinity δ v hv, Fintype.card_fin, ← Real.exp_nat_mul]
  congr 1
  ring

theorem product_affinity_integrable (n : ℕ) (δ : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    Integrable (fun x : Fin n → ℝ =>
      Real.sqrt (density n δ v x * density n (-δ) v x)) := by
  simp_rw [density_geometric_mean]
  exact Integrable.fintype_prod (fun _ => integrable_geometric_mean δ v hv)

theorem testing_radius_le_quarter (n : ℕ) (δ : ℝ) (v : ℝ≥0)
    (h : (n : ℝ) * δ ^ 2 / (v : ℝ) ≤ 1 / 16) :
    Real.sqrt (1 - Real.exp (-(n : ℝ) * δ ^ 2 / (2 * (v : ℝ))) ^ 2) ≤ 1 / 4 := by
  have he : Real.exp (-(n : ℝ) * δ ^ 2 / (2 * (v : ℝ))) ^ 2 =
      Real.exp (-((n : ℝ) * δ ^ 2 / (v : ℝ))) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [he]
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by norm_num, ?_⟩
  have hexp := Real.add_one_le_exp (-((n : ℝ) * δ ^ 2 / (v : ℝ)))
  nlinarith

end Bilevel.GaussianAffinity
