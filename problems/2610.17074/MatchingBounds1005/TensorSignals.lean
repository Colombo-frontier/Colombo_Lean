import MatchingBounds1005.TensorMasks
import MatchingBounds1005.TaperCorrection

/-! The actual cubic and quartic hidden signals and exact-core oracle algebra. -/
noncomputable section
open scoped BigOperators InnerProductSpace ContDiff

namespace MatchingBounds1005.TensorGeometry

theorem polynomial_smul {d k : ℕ} (c : ℝ) (T : Tensor d k) (x : Vec d) :
    polynomial (c • T) x = c * polynomial T x := by
  simp only [polynomial_eq_inner, real_inner_smul_left]

theorem polynomial_add {d k : ℕ} (T S : Tensor d k) (x : Vec d) :
    polynomial (T + S) x = polynomial T x + polynomial S x := by
  simp only [polynomial_eq_inner, inner_add_left]

theorem polynomial_sum {ι : Type*} {d k : ℕ} (s : Finset ι)
    (T : ι → Tensor d k) (x : Vec d) :
    polynomial (∑ i ∈ s, T i) x = ∑ i ∈ s, polynomial (T i) x := by
  simp only [polynomial_eq_inner, sum_inner]

theorem polynomial_rankOne {d : ℕ} (k : ℕ) (b x : Vec d) :
    polynomial (rankOne k b) x = ⟪b, x⟫_ℝ ^ k := by
  rw [polynomial_eq_inner, rankOne_inner]

def signal {ι : Type*} [Fintype ι] {d : ℕ} (k : ℕ) (w : ℝ)
    (b : ι → Vec d) : Tensor d k := w • ∑ s, rankOne k (b s)

theorem signal_polynomial {ι : Type*} [Fintype ι] {d : ℕ} (k : ℕ) (w : ℝ)
    (b : ι → Vec d) (x : Vec d) :
    polynomial (signal k w b) x = w * ∑ s, ⟪b s, x⟫_ℝ ^ k := by
  rw [signal, polynomial_smul, polynomial_sum]
  simp only [polynomial_rankOne]

def cubicSignal {ι : Type*} [Fintype ι] {d : ℕ} (τ A : ℝ) (b : ι → Vec d) :
    Tensor d 3 := signal 3 (-120 * τ * A ^ 3) b

def quarticSignal {ι : Type*} [Fintype ι] {d : ℕ} (τ A : ℝ) (b : ι → Vec d) :
    Tensor d 4 := signal 4 (120 * τ * A ^ 4) b

theorem signal_mask_quartic {ι : Type*} [Fintype ι] {d : ℕ}
    (τ A : ℝ) (b : ι → Vec d) (x : Vec d) :
    mask (cubicSignal τ A b) (quarticSignal τ A b) x =
      τ * ∑ s, (30 * (A * ⟪b s, x⟫_ℝ) ^ 4 - 40 * (A * ⟪b s, x⟫_ℝ) ^ 3) := by
  unfold mask cubicSignal quarticSignal
  rw [signal_polynomial, signal_polynomial]
  simp only [Finset.mul_sum, Finset.sum_sub_distrib]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- A global identity; only the correction terms need scheduled disclosure. -/
theorem potential_tensor_decomposition {ι : Type*} [Fintype ι] {d : ℕ}
    (τ r A : ℝ) (b : ι → Vec d) (x : Vec d) :
    τ * ridgeSum b (Primitive.potential r) A x =
      mask (cubicSignal τ A b) (quarticSignal τ A b) x +
      10 * τ * Fintype.card ι + τ * ridgeSum b (Primitive.correction r) A x := by
  rw [signal_mask_quartic]
  unfold ridgeSum Primitive.correction quarticCore
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  ring

theorem potential_disclosed_value {ι : Type*} [Fintype ι] {d : ℕ}
    (τ A : ℝ) (b : ι → Vec d) (S : Finset ι) {r : ℝ} (hr : 1 ≤ r)
    (x : Vec d) (hx : ∀ i, i ∉ S → |A * ⟪b i, x⟫_ℝ| ≤ r) :
    τ * ridgeSum b (Primitive.potential r) A x =
      mask (cubicSignal τ A b) (quarticSignal τ A b) x +
      10 * τ * Fintype.card ι + τ * ∑ i ∈ S, Primitive.correction r (A * ⟪b i, x⟫_ℝ) := by
  rw [potential_tensor_decomposition]
  rw [ridgeSum, (Primitive.disclosed_corrections b S hr x hx).1]

theorem potential_disclosed_derivative {ι : Type*} [Fintype ι] {d : ℕ}
    (τ A : ℝ) (b : ι → Vec d) (S : Finset ι) {r : ℝ} (hr : 1 ≤ r)
    (x : Vec d) (hx : ∀ i, i ∉ S → |A * ⟪b i, x⟫_ℝ| ≤ r) :
    fderiv ℝ (fun y => τ * ridgeSum b (Primitive.potential r) A y) x =
      fderiv ℝ (fun y => mask (cubicSignal τ A b) (quarticSignal τ A b) y +
        10 * τ * Fintype.card ι +
        τ * ∑ i ∈ S, Primitive.correction r (A * ⟪b i, y⟫_ℝ)) x := by
  classical
  have he : (fun y => τ * ridgeSum b (Primitive.potential r) A y) =
      fun y => mask (cubicSignal τ A b) (quarticSignal τ A b) y +
        10 * τ * Fintype.card ι + τ * ridgeSum b (Primitive.correction r) A y :=
    funext (potential_tensor_decomposition τ r A b)
  have hm := (mask_smooth (cubicSignal τ A b) (quarticSignal τ A b)).differentiable
    (by norm_num : (1 : WithTop ℕ∞) ≤ ∞) x
  have hc := (ridgeSum_smooth b (Primitive.correction_smooth r) A).differentiable
    (by norm_num : (1 : WithTop ℕ∞) ≤ ∞) x
  have hs : DifferentiableAt ℝ
      (fun y => ∑ i ∈ S, Primitive.correction r (A * ⟪b i, y⟫_ℝ)) x := by
    apply DifferentiableAt.sum
    intro i _
    exact ((Primitive.correction_smooth r).comp (scaledReadout b A i).contDiff).differentiable
      (by norm_num : (1 : WithTop ℕ∞) ≤ ∞) x
  rw [he, fderiv_add (hm.add_const _) (hc.const_mul τ),
    fderiv_add (hm.add_const _) (hs.const_mul τ),
    fderiv_const_mul hc τ, fderiv_const_mul hs τ]
  congr 1
  congr 1
  exact (Primitive.disclosed_corrections b S hr x hx).2

theorem gradientRow_self {d : ℕ} (k : ℕ) (x : Vec d) :
    gradientRow k x x = (k : ℝ) • rankOne k x := by
  have h (i : Fin k) : oneOutside x x i = rankOne k x := by
    unfold oneOutside rankOne
    congr 1
    funext j
    simp
  simp only [gradientRow, h, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_smul_eq_nsmul]

/-- Euler contraction recovers the polynomial value from its exact gradient
channel, including for nonsymmetric coefficient tensors. -/
theorem polynomial_euler {d k : ℕ} (hk : 1 ≤ k) (T : Tensor d k) (x : Vec d) :
    polynomial T x = (k : ℝ)⁻¹ * fderiv ℝ (polynomial T) x x := by
  rw [polynomial_fderiv_apply, gradientRow_self, real_inner_smul_right,
    ← polynomial_eq_inner]
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  field_simp

end MatchingBounds1005.TensorGeometry
