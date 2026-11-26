import MatchingBounds1005.TensorGeometry
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.Gradient.Basic

/-! Tensor polynomial masks and their genuine linear value/gradient rows. -/
noncomputable section
open scoped BigOperators InnerProductSpace ContDiff

namespace MatchingBounds1005.TensorGeometry

def tensorForm {d k : ℕ} (T : Tensor d k) :
    ContinuousMultilinearMap ℝ (fun _ : Fin k => Vec d) ℝ :=
  ∑ idx : Fin k → Fin d, T idx •
    (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin k) ℝ).compContinuousLinearMap
      (fun j => EuclideanSpace.proj (idx j))

theorem tensorForm_apply {d k : ℕ} (T : Tensor d k) (v : Fin k → Vec d) :
    tensorForm T v = ⟪T, productTensor v⟫_ℝ := by
  simp only [tensorForm, ContinuousMultilinearMap.sum_apply,
    ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebra_apply, smul_eq_mul, PiLp.inner_apply,
    RCLike.inner_apply, conj_trivial, productTensor_apply]
  apply Finset.sum_congr rfl
  intro idx _
  exact mul_comm _ _

theorem tensorForm_norm_le {d k : ℕ} (T : Tensor d k) : ‖tensorForm T‖ ≤ ‖T‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg T)
  intro v
  rw [tensorForm_apply, Real.norm_eq_abs]
  exact (abs_real_inner_le_norm T (productTensor v)).trans_eq
    (by rw [productTensor_norm])

def polynomial {d k : ℕ} (T : Tensor d k) (x : Vec d) : ℝ := tensorForm T (fun _ => x)

theorem polynomial_eq_inner {d k : ℕ} (T : Tensor d k) (x : Vec d) :
    polynomial T x = ⟪T, rankOne k x⟫_ℝ := tensorForm_apply T _

theorem polynomial_smooth {d k : ℕ} (T : Tensor d k) : ContDiff ℝ ∞ (polynomial T) :=
  (tensorForm T).contDiff.comp (contDiff_pi.mpr (fun _ => contDiff_id))

theorem polynomial_value_bound {d k : ℕ} (T : Tensor d k) (x : Vec d) :
    |polynomial T x| ≤ ‖tensorForm T‖ * ‖x‖ ^ k := by
  simpa only [polynomial, Real.norm_eq_abs, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] using (tensorForm T).le_opNorm (fun _ => x)

/-- The exact falling-factorial derivative estimate, using the actual
multilinear operator norm (not the much larger Frobenius norm). -/
theorem polynomial_derivative_bound {d k : ℕ} (T : Tensor d k) (n : ℕ) (x : Vec d) :
    ‖iteratedFDeriv ℝ n (polynomial T) x‖ ≤
      k.descFactorial n * ‖tensorForm T‖ * ‖x‖ ^ (k - n) := by
  let D : Vec d →L[ℝ] (Fin k → Vec d) :=
    ContinuousLinearMap.pi (fun _ => ContinuousLinearMap.id ℝ (Vec d))
  have hD : ‖D‖ ≤ 1 := by
    apply D.opNorm_le_bound (by norm_num)
    intro v
    change ‖fun _ : Fin k => v‖ ≤ 1 * ‖v‖
    rw [one_mul, pi_norm_le_iff_of_nonneg (norm_nonneg v)]
    exact fun _ => le_rfl
  have hx : ‖D x‖ ≤ ‖x‖ := by
    change ‖fun _ : Fin k => x‖ ≤ ‖x‖
    rw [pi_norm_le_iff_of_nonneg (norm_nonneg x)]
    exact fun _ => le_rfl
  have he : polynomial T = tensorForm T ∘ D := rfl
  have hs : ContDiff ℝ n (tensorForm T) := (tensorForm T).contDiff
  rw [he, D.iteratedFDeriv_comp_right hs x le_rfl]
  calc
    _ ≤ ‖iteratedFDeriv ℝ n (tensorForm T) (D x)‖ * ‖D‖ ^ n := by
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
        (iteratedFDeriv ℝ n (tensorForm T) (D x)).norm_compContinuousLinearMap_le
          (fun _ => D)
    _ ≤ ‖iteratedFDeriv ℝ n (tensorForm T) (D x)‖ * 1 := by
      exact mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg D) hD) (norm_nonneg _)
    _ ≤ _ := by
      rw [mul_one]
      apply ((tensorForm T).norm_iteratedFDeriv_le n (D x)).trans
      simp only [Fintype.card_fin]
      gcongr

def gradientRow {d : ℕ} (k : ℕ) (x v : Vec d) : Tensor d k :=
  ∑ i : Fin k, oneOutside x v i

theorem polynomial_fderiv_apply {d k : ℕ} (T : Tensor d k) (x v : Vec d) :
    fderiv ℝ (polynomial T) x v = ⟪T, gradientRow k x v⟫_ℝ := by
  let D : Vec d →L[ℝ] (Fin k → Vec d) :=
    ContinuousLinearMap.pi (fun _ => ContinuousLinearMap.id ℝ (Vec d))
  have h : HasFDerivAt (polynomial T)
      ((tensorForm T).linearDeriv (fun _ => x) ∘L D) x :=
    ((tensorForm T).hasFDerivAt (fun _ => x)).comp x D.hasFDerivAt
  rw [h.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousMultilinearMap.linearDeriv_apply,
    D, ContinuousLinearMap.pi_apply, ContinuousLinearMap.id_apply,
    tensorForm_apply, gradientRow, inner_sum]
  rfl

theorem rankOne_mem_observationSpace {d k : ℕ} (hk : 1 ≤ k)
    (W : Submodule ℝ (Vec d)) {x : Vec d} (hx : x ∈ W) :
    rankOne k x ∈ observationSpace k W := by
  apply Submodule.subset_span
  exact ⟨fun _ => x, ⟨0, by omega⟩, fun _ _ => hx, rfl⟩

theorem gradientRow_mem_observationSpace {d : ℕ} (k : ℕ)
    (W : Submodule ℝ (Vec d)) {x : Vec d} (hx : x ∈ W) (v : Vec d) :
    gradientRow k x v ∈ observationSpace k W := by
  apply Submodule.sum_mem
  intro i _
  apply Submodule.subset_span
  refine ⟨Function.update (fun _ => x) i v, i, ?_, rfl⟩
  intro j hji
  simpa only [Function.update_of_ne hji] using hx

end MatchingBounds1005.TensorGeometry
