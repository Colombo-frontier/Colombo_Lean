import GradientHessian.FirstHeightDerivatives

/-! Actual incoming-times-leaf-port products have bounded jets. Combined
with the proved leaf correction jets, every literal first-height payload
has the source scale M^(3-j), including its spacing and terminal terms. -/

noncomputable section
namespace GradientHessian.FirstHeight
open EuclideanRegisters InnerCoordinates LatchLocalDerivatives

def incomingProductOrder (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * (8 * localConstant j) * LatchLemma.latchConstant
def incomingProductConstant : ℝ := 1 + ∑ n ∈ Finset.range 4, incomingProductOrder n

theorem incomingProductOrder_nonneg (n : ℕ) : 0 ≤ incomingProductOrder n := by
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by have h := localConstant_pos j; positivity))
    LatchLemma.latchConstant_pos.le

theorem incomingProductConstant_pos : 0 < incomingProductConstant := by
  unfold incomingProductConstant
  have hs : 0 ≤ ∑ n ∈ Finset.range 4, incomingProductOrder n :=
    Finset.sum_nonneg (fun n _ => incomingProductOrder_nonneg n)
  linarith

theorem incomingProductOrder_le {n : ℕ} (hn : n ≤ 3) : incomingProductOrder n ≤ incomingProductConstant := by
  have hs := Finset.single_le_sum (s := Finset.range 4) (f := incomingProductOrder)
    (fun j _ => incomingProductOrder_nonneg j) (a := n) (Finset.mem_range.mpr (by omega))
  unfold incomingProductConstant
  linarith

def payloadScaleConstant (D A : ℝ) : ℝ := D + 8 * (A + 56) + incomingProductConstant

theorem payloadScaleConstant_pos {D A : ℝ} (hD : 0 ≤ D) (hA : 0 ≤ A) :
    0 < payloadScaleConstant D A := by
  unfold payloadScaleConstant
  linarith [incomingProductConstant_pos]

section LeafPort
variable {Y E : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The outgoing port is the actual last inner task's last-register port;
its derivative bound is independent of the number of inner tasks. -/
theorem inner_outgoing_derivative_bound
    (v : Fin (m + 1) → Fin (Inner.absoluteDepth + 2) → E)
    (hv : ‖v (Fin.last m) (Fin.last (Inner.absoluteDepth + 1))‖ = 1)
    (Z : InnerCoordinates.Space Y E (m + 1) (Inner.absoluteDepth + 2)) {n : ℕ} (hn : n ≤ 3) :
    ‖iteratedFDeriv ℝ n (Inner.outgoing v) Z‖ ≤ LatchLemma.latchConstant := by
  have h := Inner.derivative_comp_linear_le
    (Inner.taskProjection (Y := Y) (E := E) (m + 1) Inner.absoluteDepth (Fin.last m))
    (Inner.taskProjection_norm_le _ _ _) (Inner.completion_contDiff (v (Fin.last m))) hn Z
  apply h.trans
  have hp := LatchDerivativeSums.port_derivative_bound (Inner.absoluteDepth + 1)
    (v (Fin.last m)) (Inner.radius Inner.absoluteDepth) (Inner.radius_pos _ _) hv hn
    (Inner.taskProjection (Y := Y) (E := E) (m + 1) Inner.absoluteDepth (Fin.last m) Z)
  apply hp.trans
  rw [Inner.radius_last]
  exact (div_le_self (localConstant_pos n).le (one_le_pow₀ (Inner.lastRadius_ge_one _))).trans
    (LatchLemma.latchConstant_bounds hn).2.1

end LeafPort

variable {F E : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem incoming_product_derivative_bound (o : F → ℝ) (ho : ContDiff ℝ 3 o)
    (v : Fin b → Fin (k + 2) → E) (i : Fin b) (hv : ‖v i 0‖ = 1)
    (Z : Space F E b k)
    (hD : ∀ j, j ≤ 3 → ‖iteratedFDeriv ℝ j o (numerical F E b (k + 2) Z)‖ ≤ LatchLemma.latchConstant)
    {n : ℕ} (hn : n ≤ 3) :
    ‖iteratedFDeriv ℝ n (fun W : Space F E b k => Inner.input (v i) (tasks F E b (k + 2) W i) *
      o (numerical F E b (k + 2) W)) Z‖ ≤ incomingProductConstant := by
  let B := fun W : Space F E b k => Inner.input (v i) (tasks F E b (k + 2) W i)
  let p := fun W : Space F E b k => o (numerical F E b (k + 2) W)
  have hB : ContDiff ℝ 3 B := (Inner.input_contDiff (v i)).comp
    (Inner.taskProjection (Y := F) (E := E) b k i).contDiff
  have hp : ContDiff ℝ 3 p := ho.comp (numerical F E b (k + 2)).contDiff
  apply (norm_iteratedFDeriv_mul_le hB hp Z (by exact_mod_cast hn)).trans
  apply le_trans (b := incomingProductOrder n) _ (incomingProductOrder_le hn)
  apply Finset.sum_le_sum
  intro j hj
  have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hnj : n - j ≤ 3 := (Nat.sub_le n j).trans hn
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left (Inner.lifted_input_derivative_bound v i hv Z (hjn.trans hn))
      (Nat.cast_nonneg _)
  · exact (Inner.derivative_comp_linear_le (numerical F E b (k + 2))
      (Inner.numerical_norm_le _ _) ho hnj Z).trans (hD _ hnj)
  · exact norm_nonneg _
  · exact mul_nonneg (Nat.cast_nonneg _) (by have h := localConstant_pos j; positivity)

theorem constant_scaled_bound {M C c : ℝ} (hM : 1 ≤ M) (hC : 0 ≤ C) (hc : |c| ≤ C * M)
    (Z : F) {n : ℕ} (hn : n ≤ 3) :
    ‖iteratedFDeriv ℝ n (fun _ : F => c) Z‖ ≤ C * M ^ (3 - n) := by
  by_cases hz : n = 0
  · subst n
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    have hp : M ≤ M ^ 3 := by
      simpa using pow_le_pow_right₀ hM (by norm_num : (1 : ℕ) ≤ 3)
    exact hc.trans (mul_le_mul_of_nonneg_left hp hC)
  · rw [iteratedFDeriv_const_of_ne hz, Pi.zero_apply, norm_zero]
    exact mul_nonneg hC (pow_nonneg (zero_le_one.trans hM) _)

theorem spacing_abs_bound {M A : ℝ} (hM : 1 ≤ M) (hA : 0 ≤ A) (i : Fin 8) :
    |(i.val : ℝ) * (A * M + 56)| ≤ (8 * (A + 56)) * M := by
  have hm : 0 ≤ M := zero_le_one.trans hM
  have hi : (i.val : ℝ) ≤ 8 := by exact_mod_cast i.isLt.le
  have hS : 0 ≤ A * M + 56 := by positivity
  rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg i.val) hS)]
  have hs : A * M + 56 ≤ (A + 56) * M := by nlinarith
  have h := mul_le_mul hi hs hS (by norm_num : (0 : ℝ) ≤ 8)
  nlinarith

theorem payload_scaled_bound {M D A : ℝ} (hM : 1 ≤ M) (hA : 0 ≤ A)
    (Q : F → ℝ) (child childPort : Fin 8 → F → ℝ)
    (v : Fin 8 → Fin (k + 2) → E) (hQ : ContDiff ℝ 3 Q)
    (hc : ∀ i, ContDiff ℝ 3 (child i)) (ho : ∀ i, ContDiff ℝ 3 (childPort i))
    (Z : Space F E 8 k) (i : Fin 8) (hv : ‖v i 0‖ = 1)
    (hrel : ∀ j, j ≤ 3 → ‖iteratedFDeriv ℝ j (fun x => child i x - Q x)
      (numerical F E 8 (k + 2) Z)‖ ≤ D * M ^ (3 - j))
    (hop : ∀ j, j ≤ 3 → ‖iteratedFDeriv ℝ j (childPort i)
      (numerical F E 8 (k + 2) Z)‖ ≤ LatchLemma.latchConstant)
    {n : ℕ} (hn : n ≤ 3) :
    ‖iteratedFDeriv ℝ n (fun W => payload Q child childPort (A * M + 56) v W i) Z‖ ≤
      payloadScaleConstant D A * M ^ (3 - n) := by
  let r := fun W : Space F E 8 k => child i (numerical F E 8 (k + 2) W) - Q (numerical F E 8 (k + 2) W)
  let s := fun _ : Space F E 8 k => (i.val : ℝ) * (A * M + 56)
  let p := fun W : Space F E 8 k => Inner.input (v i) (tasks F E 8 (k + 2) W i) *
    childPort i (numerical F E 8 (k + 2) W)
  have hr : ContDiff ℝ 3 r := ((hc i).sub hQ).comp (numerical F E 8 (k + 2)).contDiff
  have hs : ContDiff ℝ 3 s := contDiff_const
  have hp : ContDiff ℝ 3 p :=
    ((Inner.input_contDiff (v i)).comp (Inner.taskProjection (Y := F) (E := E) 8 k i).contDiff).mul
      ((ho i).comp (numerical F E 8 (k + 2)).contDiff)
  have hsplit := LocalizedProductDerivatives.norm_iteratedFDeriv_sub_le (x := Z) (n := n)
    ((hr.sub hs).of_le (by exact_mod_cast hn)).contDiffAt (hp.of_le (by exact_mod_cast hn)).contDiffAt
  have hsplit2 := LocalizedProductDerivatives.norm_iteratedFDeriv_sub_le (x := Z) (n := n)
    (hr.of_le (by exact_mod_cast hn)).contDiffAt (hs.of_le (by exact_mod_cast hn)).contDiffAt
  have hR := (Inner.derivative_comp_linear_le (numerical F E 8 (k + 2))
    (Inner.numerical_norm_le _ _) ((hc i).sub hQ) hn Z).trans (hrel n hn)
  have hS := constant_scaled_bound hM (by positivity : 0 ≤ 8 * (A + 56))
    (spacing_abs_bound hM hA i) Z hn
  have hP := incoming_product_derivative_bound (childPort i) (ho i) v i hv Z hop hn
  have hpow : 1 ≤ M ^ (3 - n) := one_le_pow₀ hM
  have hprod := le_mul_of_one_le_right incomingProductConstant_pos.le hpow
  change ‖iteratedFDeriv ℝ n (fun W => r W - s W - p W) Z‖ ≤ _
  change ‖iteratedFDeriv ℝ n r Z‖ ≤ _ at hR
  change ‖iteratedFDeriv ℝ n s Z‖ ≤ _ at hS
  change ‖iteratedFDeriv ℝ n p Z‖ ≤ _ at hP
  unfold payloadScaleConstant
  nlinarith

end GradientHessian.FirstHeight
