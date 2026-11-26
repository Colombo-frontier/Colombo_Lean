import GradientHessian.FirstHeightFunctions
import GradientHessian.FirstHeightScales

/-! Source-scale derivative transfer through the actual first-height
selector. The ratio R ≥ M removes every task-count/scale factor. -/

noncomputable section
namespace GradientHessian.FirstHeight
open EuclideanRegisters InnerCoordinates SelectorPayloadBounds SelectorMassBounds SelectorVectorBounds

variable {F E : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem selected_eq_weightedScalar (Q : F → ℝ) (child childPort : Fin b → F → ℝ) (S : ℝ)
    (v : Fin b → Fin (k + 2) → E) :
    selected Q child childPort S v = weightedScalar (Inner.lastRadius k)
      (fun i => v i (Fin.last (k + 1))) (Inner.lastProjection (Y := F) (E := E) b k)
      (fun i Z => payload Q child childPort S v Z i) (fun _ => -(b : ℝ) * S) := by
  funext Z
  simp only [selected, FirstHeightSelector.select_eq_inner, weightedScalar]
  have hp : Inner.ports v Z = fun i => SelectorPortJets.coordinatePort (Inner.lastRadius k)
      (fun i => v i (Fin.last (k + 1))) (Inner.lastProjection (Y := F) (E := E) b k) i Z := by
    funext i
    exact Inner.ports_eq_selectorPort v Z i
  rw [hp]

/-- The exact product-rule estimate at R≥M becomes C M^(3-n). Payload
derivative premises are about the actual functions, and later supplied by
the proved capped-leaf and incoming-port product estimates. -/
theorem selected_scaled_bound {M C : ℝ} (hM : 0 < M) (hC : 0 ≤ C)
    (Q : F → ℝ) (child childPort : Fin b → F → ℝ) (S : ℝ)
    (v : Fin b → Fin (k + 2) → E) (hQ : ContDiff ℝ 3 Q)
    (hc : ∀ i, ContDiff ℝ 3 (child i)) (ho : ∀ i, ContDiff ℝ 3 (childPort i))
    (hv : ∀ i, ‖v i (Fin.last (k + 1))‖ = 1) (hR : M ≤ Inner.lastRadius k)
    (Z : Space F E b k)
    (hD : ∀ i j, j ≤ 3 → ‖iteratedFDeriv ℝ j (fun W => payload Q child childPort S v W i) Z‖ ≤
      C * M ^ (3 - j))
    (hT : ∀ j, j ≤ 3 → ‖iteratedFDeriv ℝ j (fun _ : Space F E b k => -(b : ℝ) * S) Z‖ ≤
      C * M ^ (3 - j)) {n : ℕ} (hn : n ≤ 3) :
    ‖iteratedFDeriv ℝ n (selected Q child childPort S v) Z‖ ≤
      C * uniformOrderConstant n * M ^ (3 - n) := by
  rw [selected_eq_weightedScalar]
  have hr : 0 < Inner.lastRadius k := hM.trans_le hR
  apply (weightedScalar_derivative_bound hr hC hM.le _ hv _
    (Inner.lastProjection_coordinate_contraction b k) _ _
    (payload_contDiff Q child childPort S v hQ hc ho) contDiff_const Z hD hT hn).trans
  have hsum : (∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) *
      (massConstant j / Inner.lastRadius k ^ j) * (C * M ^ (3 - (n - j)))) ≤
      ∑ j ∈ Finset.range (n + 1), C * ((n.choose j : ℝ) * massConstant j) * M ^ (3 - n) := by
    apply Finset.sum_le_sum
    intro j hj
    have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hexp : 3 - (n - j) = (3 - n) + j := by omega
    have hp : M ^ j / Inner.lastRadius k ^ j ≤ 1 :=
      (div_le_one (pow_pos hr j)).mpr (pow_le_pow_left₀ hM.le hR j)
    have hm := mul_le_mul_of_nonneg_left hp
      (mul_nonneg (mul_nonneg hC (mul_nonneg (Nat.cast_nonneg (n.choose j)) (massConstant_nonneg j)))
        (pow_nonneg hM.le (3 - n)))
    rw [hexp, pow_add]
    convert hm using 1 <;> ring
  apply hsum.trans_eq
  simp only [uniformOrderConstant, Finset.mul_sum, Finset.sum_mul]

end GradientHessian.FirstHeight
