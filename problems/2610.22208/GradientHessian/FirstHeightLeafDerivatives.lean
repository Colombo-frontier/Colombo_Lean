import GradientHessian.FirstHeightLeafData
import GradientHessian.FirstHeightPayloadDerivatives
import GradientHessian.LeafDerivatives

/-! Actual first-height residual derivative bounds. Leaf correction jets,
incoming products, the selector and the eight self residuals are all proved
from their literal formulas; no first-height derivative premise is used. -/

noncomputable section
namespace GradientHessian.FirstHeight
open InnerCoordinates SelectorPayloadBounds

def firstPayloadConstant : ℝ := payloadScaleConstant Leaf.leafJetConstant leafValueConstant
def selectorOrderSum : ℝ := 1 + ∑ n ∈ Finset.range 4, uniformOrderConstant n
def firstDerivativeConstant : ℝ := 9 * LatchLemma.latchConstant + firstPayloadConstant * selectorOrderSum

theorem firstPayloadConstant_pos : 0 < firstPayloadConstant :=
  payloadScaleConstant_pos Leaf.leafJetConstant_pos.le leafValueConstant_pos.le
theorem selectorOrderSum_pos : 0 < selectorOrderSum := by
  have hs : 0 ≤ ∑ n ∈ Finset.range 4, uniformOrderConstant n :=
    Finset.sum_nonneg (fun n _ => uniformOrderConstant_nonneg n)
  unfold selectorOrderSum
  linarith
theorem uniformOrderConstant_le {n : ℕ} (hn : n ≤ 3) : uniformOrderConstant n ≤ selectorOrderSum := by
  have hs := Finset.single_le_sum (s := Finset.range 4) (f := uniformOrderConstant)
    (fun n _ => uniformOrderConstant_nonneg n) (a := n) (Finset.mem_range.mpr (by omega))
  unfold selectorOrderSum
  linarith
theorem firstDerivativeConstant_pos : 0 < firstDerivativeConstant := by
  unfold firstDerivativeConstant
  have hp := mul_pos firstPayloadConstant_pos selectorOrderSum_pos
  linarith [LatchLemma.latchConstant_pos]

variable {Y E : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem sourcePayload_derivative_bound (d : Data Y E m) (hd : Valid d)
    (Z : SourceSpace Y E m) (i : Fin 8) {n : ℕ} (hn : n ≤ 3) :
    ‖iteratedFDeriv ℝ n (fun W => payload (Leaf.publicQuadratic (m + 1)) (children d) (childPorts d)
      (spacing m) d.outerDirections W i) Z‖ ≤ firstPayloadConstant * (m + 1 : ℝ) ^ (3 - n) := by
  apply payload_scaled_bound (by exact_mod_cast (show 1 ≤ m + 1 by omega)) leafValueConstant_pos.le
    (Leaf.publicQuadratic (m + 1)) (children d) (childPorts d) d.outerDirections
    (Leaf.publicQuadratic_contDiff _) (children_contDiff d) (childPorts_contDiff d)
    Z i (hd.outer_unit i 0) ?_ ?_ hn
  · intro j hj
    rw [funext (children_relative d i)]
    simpa only [Nat.cast_add, Nat.cast_one] using
      Leaf.correction_derivative_bound (m := m + 1) (by omega) (d.A i)
        (by simpa using hd.opNorm i) (d.b i) (d.a i) (d.innerDirections i)
        (hd.b_norm i) (hd.a_norm i) (hd.inner_unit i)
        (numerical (Leaf.Space Y E (m + 1)) E 8 (depth (m + 1) + 2) Z) hj
  · intro j hj
    exact inner_outgoing_derivative_bound (d.innerDirections i) (hd.inner_unit i _ _) _ hj

omit [CompleteSpace Y] [CompleteSpace E] in
theorem sourceTerminal_derivative_bound (m : ℕ) (Z : SourceSpace Y E m) {n : ℕ} (hn : n ≤ 3) :
    ‖iteratedFDeriv ℝ n (fun _ : SourceSpace Y E m => -(8 : ℝ) * spacing m) Z‖ ≤
      firstPayloadConstant * (m + 1 : ℝ) ^ (3 - n) := by
  have hm : (1 : ℝ) ≤ m + 1 := by exact_mod_cast (show 1 ≤ m + 1 by omega)
  have hcoef : 0 ≤ 8 * (leafValueConstant + 56) := by have h := leafValueConstant_pos; positivity
  have habs : |-(8 : ℝ) * spacing m| ≤ (8 * (leafValueConstant + 56)) * (m + 1) := by
    have hS := spacing_ge m
    rw [abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 8),
      abs_of_nonneg (le_trans (by norm_num) hS)]
    unfold spacing
    nlinarith
  have h := constant_scaled_bound hm hcoef habs Z hn
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  unfold firstPayloadConstant payloadScaleConstant
  linarith [Leaf.leafJetConstant_pos, incomingProductConstant_pos]

theorem sourceSelected_derivative_bound (d : Data Y E m) (hd : Valid d) (Z : SourceSpace Y E m)
    {n : ℕ} (hn : n ≤ 3) :
    ‖iteratedFDeriv ℝ n (selected (Leaf.publicQuadratic (m + 1)) (children d) (childPorts d)
      (spacing m) d.outerDirections) Z‖ ≤
      firstPayloadConstant * selectorOrderSum * (m + 1 : ℝ) ^ (3 - n) := by
  have hm : (0 : ℝ) < m + 1 := by positivity
  have hR : (m + 1 : ℝ) ≤ Inner.lastRadius (depth (m + 1)) := by
    have h := (outerRadius_range (M := m + 1) (by omega)).1
    simp only [Nat.cast_add, Nat.cast_one, outerRadius] at h
    linarith
  have h := selected_scaled_bound hm firstPayloadConstant_pos.le
    (Leaf.publicQuadratic (m + 1)) (children d) (childPorts d) (spacing m) d.outerDirections
    (Leaf.publicQuadratic_contDiff _) (children_contDiff d) (childPorts_contDiff d)
    (fun i => hd.outer_unit i _) hR Z (fun i j hj => sourcePayload_derivative_bound d hd Z i hj)
    (fun j hj => sourceTerminal_derivative_bound m Z hj) hn
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (uniformOrderConstant_le hn) firstPayloadConstant_pos.le) (by positivity))

theorem sourceSelf_derivative_bound (d : Data Y E m) (hd : Valid d) (Z : SourceSpace Y E m)
    {n : ℕ} (hn0 : 1 ≤ n) (hn : n ≤ 3) :
    ‖iteratedFDeriv ℝ n (Inner.sumResidual d.outerDirections) Z‖ ≤
      9 * LatchLemma.latchConstant * (m + 1 : ℝ) ^ (3 - n) := by
  have hC := LatchLemma.latchConstant_pos
  have hm : (1 : ℝ) ≤ m + 1 := by exact_mod_cast (show 1 ≤ m + 1 by omega)
  interval_cases n
  · simpa only [Nat.cast_add, Nat.cast_one] using
      self_first_derivative_bound (M := m + 1) (by omega) d.outerDirections hd.outer_unit Z
  · have h := Inner.sumResidual_second_derivative_bound d.outerDirections hd.outer_unit Z
    norm_num only [Nat.reduceSub, pow_one]
    have hp := mul_le_mul_of_nonneg_left hm hC.le
    nlinarith
  · have h := Inner.sumResidual_third_derivative_bound d.outerDirections hd.outer_unit Z
    norm_num only [Nat.sub_self, pow_zero, mul_one]
    linarith

/-- Assertion (iii) of `lem:first-height`, with one absolute constant and
the actual Euclidean multilinear derivative norm. -/
theorem sourceResidual_derivative_bound (d : Data Y E m) (hd : Valid d) (Z : SourceSpace Y E m)
    {n : ℕ} (hn0 : 1 ≤ n) (hn : n ≤ 3) :
    ‖iteratedFDeriv ℝ n (sourceResidual d) Z‖ ≤ firstDerivativeConstant * (m + 1 : ℝ) ^ (3 - n) := by
  have he : sourceResidual d = fun W =>
      selected (Leaf.publicQuadratic (m + 1)) (children d) (childPorts d) (spacing m) d.outerDirections W +
        Inner.sumResidual d.outerDirections W := funext (residual_eq _ _ _ _ _)
  rw [he]
  have hsum := Inner.norm_iteratedFDeriv_add_le
    (selected_contDiff _ _ _ (spacing m) d.outerDirections (Leaf.publicQuadratic_contDiff _)
      (children_contDiff d) (childPorts_contDiff d))
    (Inner.sumResidual_contDiff d.outerDirections) hn Z
  have hs := sourceSelected_derivative_bound d hd Z hn
  have hv := sourceSelf_derivative_bound d hd Z hn0 hn
  unfold firstDerivativeConstant
  nlinarith

end GradientHessian.FirstHeight
