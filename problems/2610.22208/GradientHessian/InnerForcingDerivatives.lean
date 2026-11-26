import GradientHessian.InnerPayloadDerivatives
import GradientHessian.InnerSelectorCoordinates
import GradientHessian.SelectorPayloadBounds

/-! The literal negative forcing sum has absolute first, second and third
derivative norms, uniformly in the number of tasks and all dimensions. -/

noncomputable section
namespace GradientHessian.Inner

open EuclideanRegisters InnerCoordinates InverseGate SelectorPayloadBounds

def forcingOrderConstant (n : ℕ) : ℝ := payloadJetConstant * uniformOrderConstant n
def forcingJetConstant : ℝ := 1 + ∑ n ∈ Finset.range 4, forcingOrderConstant n

theorem forcingOrderConstant_nonneg (n : ℕ) : 0 ≤ forcingOrderConstant n :=
  mul_nonneg payloadJetConstant_pos.le (uniformOrderConstant_nonneg n)
theorem forcingJetConstant_pos : 0 < forcingJetConstant := by
  unfold forcingJetConstant
  have hs : 0 ≤ ∑ n ∈ Finset.range 4, forcingOrderConstant n :=
    Finset.sum_nonneg (fun n _ => forcingOrderConstant_nonneg n)
  linarith

variable {Y E : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem forcingSum_eq_weightedScalar (b a : Fin m → Y) (v : Fin m → Fin (k + 2) → E) :
    forcingSum b a v = weightedScalar (lastRadius k) (fun i => v i (Fin.last (k + 1)))
      (lastProjection (Y := Y) (E := E) m k) (fun i Z => payload b a v Z i) (fun _ => 0) := by
  funext Z
  simp only [forcingSum, weightedScalar, mul_zero, add_zero]
  congr 1
  funext i
  exact ports_eq_selectorPort v Z i

theorem lastRadius_ge_one (k : ℕ) : 1 ≤ lastRadius k := by
  exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)

theorem forcingSum_order_derivative_bound (b a : Fin m → Y) (v : Fin m → Fin (k + 2) → E)
    (hb : ∀ i, ‖b i‖ = H₀) (ha : ∀ i, ‖a i‖ = 1) (hv : ∀ i j, ‖v i j‖ = 1)
    (Z : Space Y E m (k + 2)) {n : ℕ} (hn : n ≤ 3) :
    ‖iteratedFDeriv ℝ n (forcingSum b a v) Z‖ ≤ forcingOrderConstant n := by
  rw [forcingSum_eq_weightedScalar]
  apply weightedScalar_uniform_bound (lastRadius_ge_one k) payloadJetConstant_pos.le
    (fun i => v i (Fin.last (k + 1))) (fun i => hv i _)
    (lastProjection (Y := Y) (E := E) m k) (lastProjection_coordinate_contraction m k)
    (fun i W => payload b a v W i) (fun _ => 0) (payload_contDiff b a v) contDiff_const Z
    (fun i j hj => payload_derivative_bound b a v i (hb i) (ha i) (hv i 0) Z hj) ?_ hn
  intro j _
  rw [iteratedFDeriv_zero_fun, Pi.zero_apply, norm_zero]
  exact payloadJetConstant_pos.le

theorem forcingSum_derivative_bound (b a : Fin m → Y) (v : Fin m → Fin (k + 2) → E)
    (hb : ∀ i, ‖b i‖ = H₀) (ha : ∀ i, ‖a i‖ = 1) (hv : ∀ i j, ‖v i j‖ = 1)
    (Z : Space Y E m (k + 2)) {n : ℕ} (hn : n ≤ 3) :
    ‖iteratedFDeriv ℝ n (forcingSum b a v) Z‖ ≤ forcingJetConstant := by
  apply (forcingSum_order_derivative_bound b a v hb ha hv Z hn).trans
  have hs := Finset.single_le_sum (s := Finset.range 4) (f := forcingOrderConstant)
    (fun j _ => forcingOrderConstant_nonneg j) (a := n) (Finset.mem_range.mpr (by omega))
  unfold forcingJetConstant
  linarith

end GradientHessian.Inner
