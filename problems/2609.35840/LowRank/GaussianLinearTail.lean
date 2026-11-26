import LowRank.GaussianMatrixRows
import Mathlib.Probability.Moments.SubGaussian

/-! Exact moment generating functions and Gaussian tails for linear
observations of the actual iid matrix law. -/

namespace LowRank
open Matrix MeasureTheory ProbabilityTheory
open scoped Matrix BigOperators
noncomputable section

theorem iidVectorLaw_exp_integral (n : ℕ) (v : NNReal) (c : Fin n → ℝ) :
    (∫ x, Real.exp (c ⬝ᵥ x) ∂iidVectorLaw n v) =
      Real.exp ((v : ℝ) / 2 * (c ⬝ᵥ c)) := by
  have he (x : Fin n → ℝ) : Real.exp (c ⬝ᵥ x) = ∏ i, Real.exp (c i * x i) := by
    exact Real.exp_sum _ _
  simp_rw [he]
  have hp : (∫ x, ∏ i, Real.exp (c i * x i) ∂iidVectorLaw n v) =
      ∏ i, ∫ z : ℝ, Real.exp (c i * z) ∂gaussianReal 0 v := by
    letI : MeasureSpace ℝ := ⟨gaussianReal 0 v⟩
    letI : SigmaFinite (volume : Measure ℝ) := by change SigmaFinite (gaussianReal 0 v); infer_instance
    exact integral_fintype_prod_eq_prod (Fin n) (fun i z => Real.exp (c i * z))
  rw [hp]
  have hg (i : Fin n) : (∫ z : ℝ, Real.exp (c i * z) ∂gaussianReal 0 v) =
      Real.exp ((v : ℝ) * (c i) ^ 2 / 2) := by
    simpa only [mgf, id_eq, zero_mul, zero_add] using
      (mgf_gaussianReal (μ := 0) (v := v) (X := id) (p := gaussianReal 0 v) (by simp) (c i))
  simp_rw [hg]
  rw [← Real.exp_sum]
  congr 1
  simp only [dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem iidMatrixLaw_exp_integral (r s : ℕ) (v : NNReal) (C : Matrix (Fin r) (Fin s) ℝ) :
    (∫ X, Real.exp (∑ i, ∑ j, C i j * X i j) ∂iidMatrixLaw r s v) =
      Real.exp ((v : ℝ) / 2 * ∑ i, ∑ j, C i j * C i j) := by
  simp_rw [Real.exp_sum]
  have hp : (∫ X, ∏ i, ∏ j, Real.exp (C i j * X i j) ∂iidMatrixLaw r s v) =
      ∏ i, ∫ x, ∏ j, Real.exp (C i j * x j) ∂iidVectorLaw s v := by
    letI : MeasureSpace (Fin s → ℝ) := ⟨iidVectorLaw s v⟩
    letI : SigmaFinite (volume : Measure (Fin s → ℝ)) := by change SigmaFinite (iidVectorLaw s v); infer_instance
    exact integral_fintype_prod_eq_prod (Fin r) (E := fun _ => Fin s → ℝ)
      (fun i (x : Fin s → ℝ) => ∏ j, Real.exp (C i j * x j))
  rw [hp]
  simp_rw [← Real.exp_sum]
  simp_rw [show ∀ i, (∫ x, Real.exp (∑ j, C i j * x j) ∂iidVectorLaw s v) =
      Real.exp ((v : ℝ) / 2 * ∑ j, C i j * C i j) from fun i => iidVectorLaw_exp_integral s v (C i)]
  rw [← Real.exp_sum, ← Finset.mul_sum]

theorem iidMatrixLaw_bilinear_mgf {r s : ℕ} (v : NNReal) (u : Fin r → ℝ) (w : Fin s → ℝ)
    (t : ℝ) :
    mgf (fun X => u ⬝ᵥ (X *ᵥ w)) (iidMatrixLaw r s v) t =
      Real.exp ((v : ℝ) * t ^ 2 / 2 * (u ⬝ᵥ u) * (w ⬝ᵥ w)) := by
  have he (X : Matrix (Fin r) (Fin s) ℝ) :
      t * (u ⬝ᵥ (X *ᵥ w)) = ∑ i, ∑ j, (t * u i * w j) * X i j := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    congr 1
    funext i
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [mgf, he]
  rw [iidMatrixLaw_exp_integral]
  congr 1
  simp only [dotProduct, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem iidMatrixLaw_bilinear_subgaussian {r s : ℕ} (v : NNReal)
    (u : Fin r → ℝ) (w : Fin s → ℝ) (hu : u ⬝ᵥ u = 1) (hw : w ⬝ᵥ w = 1) :
    HasSubgaussianMGF (fun X => u ⬝ᵥ (X *ᵥ w)) v (iidMatrixLaw r s v) := by
  constructor
  · intro t
    apply Integrable.of_integral_ne_zero
    change mgf _ _ t ≠ 0
    rw [iidMatrixLaw_bilinear_mgf]
    exact Real.exp_ne_zero _
  · intro t
    rw [iidMatrixLaw_bilinear_mgf, hu, hw, mul_one, mul_one]

theorem iidMatrixLaw_bilinear_abs_tail {r s : ℕ} (v : NNReal)
    (u : Fin r → ℝ) (w : Fin s → ℝ) (hu : u ⬝ᵥ u = 1) (hw : w ⬝ᵥ w = 1)
    {t : ℝ} (ht : 0 ≤ t) :
    (iidMatrixLaw r s v).real {X | t ≤ |u ⬝ᵥ (X *ᵥ w)|} ≤
      2 * Real.exp (-t ^ 2 / (2 * (v : ℝ))) := by
  have hpos := (iidMatrixLaw_bilinear_subgaussian v u w hu hw).measure_ge_le ht
  have hneg := (iidMatrixLaw_bilinear_subgaussian v (-u) w (by simpa using hu) hw).measure_ge_le ht
  have heq : {X : Matrix (Fin r) (Fin s) ℝ | t ≤ |u ⬝ᵥ (X *ᵥ w)|} =
      {X | t ≤ u ⬝ᵥ (X *ᵥ w)} ∪ {X | t ≤ (-u) ⬝ᵥ (X *ᵥ w)} := by
    ext X
    simp only [Set.mem_setOf_eq, Set.mem_union, neg_dotProduct, le_abs]
  rw [heq]
  have h := measureReal_union_le (μ := iidMatrixLaw r s v)
    {X | t ≤ u ⬝ᵥ (X *ᵥ w)} {X | t ≤ (-u) ⬝ᵥ (X *ᵥ w)}
  linarith

end
end LowRank
