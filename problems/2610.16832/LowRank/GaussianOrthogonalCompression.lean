import LowRank.GaussianCoordinates
import LowRank.OrderedMatrixSpectrum
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-! Orthogonal column compression of an actual iid Gaussian vector has
the iid Gaussian law in the smaller dimension, with unchanged variance. -/

namespace LowRank
open Matrix MeasureTheory ProbabilityTheory Complex
open scoped Matrix BigOperators
noncomputable section

theorem vector_measure_eq_of_characteristic {n : ℕ} {μ ν : Measure (Fin n → ℝ)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ c : Fin n → ℝ,
      (∫ x, Complex.exp ((c ⬝ᵥ x : ℝ) * Complex.I) ∂μ) =
        ∫ x, Complex.exp ((c ⬝ᵥ x : ℝ) * Complex.I) ∂ν) : μ = ν := by
  let L := (1 : Matrix (Fin n) (Fin n) ℝ).toBilin'
  have hL (x y : Fin n → ℝ) : L x y = x ⬝ᵥ y := by
    simp only [L, Matrix.toBilin'_apply', Matrix.one_mulVec]
  refine ext_of_integral_char_eq Real.continuous_probChar Real.probChar_ne_one
    (L := L) ?_ ?_ ?_
  · intro x hx hz
    have hxx : x ⬝ᵥ x = 0 := by
      rw [← hL, hz]
      rfl
    exact hx (dotProduct_self_eq_zero.mp hxx)
  · simp only [hL, dotProduct]
    fun_prop
  · intro c
    simpa only [BoundedContinuousFunction.char_apply, Real.probChar_apply, hL, dotProduct_comm] using h c

theorem iidVectorLaw_characteristic (n : ℕ) (v : NNReal) (c : Fin n → ℝ) :
    (∫ x, Complex.exp ((c ⬝ᵥ x : ℝ) * Complex.I) ∂iidVectorLaw n v) =
      Complex.exp (-((v : ℝ) : ℂ) * (c ⬝ᵥ c : ℝ) / 2) := by
  have he (x : Fin n → ℝ) : Complex.exp ((c ⬝ᵥ x : ℝ) * Complex.I) =
      ∏ i, Complex.exp ((c i : ℂ) * (x i : ℂ) * Complex.I) := by
    simp only [dotProduct, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul, Complex.exp_sum]
  simp_rw [he]
  have hp : (∫ x, ∏ i, Complex.exp ((c i : ℂ) * (x i : ℂ) * Complex.I) ∂iidVectorLaw n v) =
      ∏ i, ∫ z : ℝ, Complex.exp ((c i : ℂ) * (z : ℂ) * Complex.I) ∂gaussianReal 0 v := by
    letI : MeasureSpace ℝ := ⟨gaussianReal 0 v⟩
    letI : SigmaFinite (volume : Measure ℝ) := by change SigmaFinite (gaussianReal 0 v); infer_instance
    exact integral_fintype_prod_eq_prod (Fin n) (fun i (z : ℝ) => Complex.exp ((c i : ℂ) * z * Complex.I))
  rw [hp]
  have hg (i : Fin n) : (∫ z : ℝ, Complex.exp ((c i : ℂ) * (z : ℂ) * Complex.I) ∂gaussianReal 0 v) =
      Complex.exp (-((v : ℝ) : ℂ) * (c i : ℂ) ^ 2 / 2) := by
    simpa only [charFun_apply_real, Complex.ofReal_zero, mul_zero, zero_mul, zero_sub,
      neg_mul, neg_div] using charFun_gaussianReal (μ := 0) (v := v) (c i)
  simp_rw [hg]
  rw [← Complex.exp_sum]
  congr 1
  simp only [dotProduct, Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem iidVectorLaw_orthogonal_compression {d m : ℕ}
    (B : Matrix (Fin d) (Fin m) ℝ) (hB : Bᵀ * B = 1) (v : NNReal) :
    (iidVectorLaw d v).map (fun x => Bᵀ *ᵥ x) = iidVectorLaw m v := by
  have hm : Measurable (fun x : Fin d → ℝ => Bᵀ *ᵥ x) := by
    apply measurable_pi_lambda
    intro i
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  apply vector_measure_eq_of_characteristic
  intro c
  have hf : StronglyMeasurable (fun x : Fin m → ℝ => Complex.exp ((c ⬝ᵥ x : ℝ) * Complex.I)) :=
    (by fun_prop : Continuous _).stronglyMeasurable
  rw [integral_map_of_stronglyMeasurable hm hf]
  have he (x : Fin d → ℝ) : c ⬝ᵥ (Bᵀ *ᵥ x) = (B *ᵥ c) ⬝ᵥ x := by
    rw [dotProduct_mulVec, Matrix.vecMul_transpose]
  simp_rw [he]
  rw [iidVectorLaw_characteristic, iidVectorLaw_characteristic, orthogonal_columns_dot B hB]

end
end LowRank
