import GradientHessian.FirstHeightLemma

/-! Additional base facts for the higher-height induction: one global leaf
loss, the exact zero value, and radius-scaled outgoing-port derivatives. -/

noncomputable section
namespace GradientHessian.FirstHeight
open InnerCoordinates

variable {Y E : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem sourceResidual_global_lower (d : Data Y E m) (hd : Valid d) (Z : SourceSpace Y E m) :
    -firstAmplitude m - Leaf.leafJetConstant * (m + 1 : ℝ) ^ 3 ≤ sourceResidual d Z := by
  let z := numerical (Leaf.Space Y E (m + 1)) E 8 (depth (m + 1) + 2) Z
  let C := Leaf.leafJetConstant * (m + 1 : ℝ) ^ 3
  have hC : 0 ≤ C := mul_nonneg Leaf.leafJetConstant_pos.le (by positivity)
  have hchild (i : Fin 8) : Leaf.publicQuadratic (m + 1) z - C ≤ children d i z := by
    have h := Leaf.correction_derivative_bound (m := m + 1) (by omega) (d.A i)
      (by simpa using hd.opNorm i) (d.b i) (d.a i) (d.innerDirections i)
      (hd.b_norm i) (hd.a_norm i) (hd.inner_unit i) z (n := 0) (by norm_num)
    simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, Nat.sub_zero, Nat.cast_add, Nat.cast_one] at h
    have hh := (abs_le.mp h).1
    rw [← children_relative d i z] at hh
    dsimp only [C]
    linarith
  have h := global_energy (Leaf.publicQuadratic (m + 1)) (children d) (childPorts d)
    (H := Leaf.publicQuadratic (m + 1) z - C) (C := 0) (spacing_ge m) le_rfl
    d.outerDirections Z (by linarith) (by intro i; simpa using hchild i)
    (fun i => childPorts_bounds d i z)
  change -(amplitude 8 (spacing m) (outerRadius (m + 1))) - C ≤
    node (Leaf.publicQuadratic (m + 1)) (children d) (childPorts d) (spacing m) d.outerDirections Z -
      (Leaf.publicQuadratic (m + 1) z + Inner.publicQuadratic 8 (depth (m + 1)) Z)
  change _ ≤ node (Leaf.publicQuadratic (m + 1)) (children d) (childPorts d) (spacing m) d.outerDirections Z at h
  unfold outerRadius
  linarith

omit [CompleteSpace Y] [CompleteSpace E] in
theorem sourceOutgoing_zero (d : Data Y E m) : sourceOutgoing d (0 : SourceSpace Y E m) = 0 :=
  Leaf.inner_ports_zero d.outerDirections (Fin.last 7)

omit [CompleteSpace Y] [CompleteSpace E] in
theorem sourceNode_zero (d : Data Y E m) : sourceNode d (0 : SourceSpace Y E m) = -10 * InverseGate.H₀ ^ 2 := by
  have hp (i : Fin 8) : Inner.ports d.outerDirections (0 : SourceSpace Y E m) i = 0 :=
    Leaf.inner_ports_zero d.outerDirections i
  have ho (i : Fin 8) : childPorts d i (0 : Leaf.Space Y E (m + 1)) = 0 :=
    Leaf.inner_ports_zero (d.innerDirections i) (Fin.last m)
  simp only [sourceNode, node, selected, FirstHeightSelector.select, hp,
    sub_zero, one_mul, zero_mul, add_zero, map_zero]
  simp [payload, ho, children, Leaf.objective_zero, Leaf.publicQuadratic, Inner.publicQuadratic,
    LatchChain.publicQuadratic, Inner.selfSum, Leaf.inner_block_zero]

omit [CompleteSpace Y] [CompleteSpace E] in
theorem sourceOutgoing_derivative_bound (d : Data Y E m)
    (hv : ‖d.outerDirections (Fin.last 7) (Fin.last (depth (m + 1) + 1))‖ = 1)
    (Z : SourceSpace Y E m) {n : ℕ} (hn : n ≤ 3) :
    ‖iteratedFDeriv ℝ n (sourceOutgoing d) Z‖ ≤ LatchLemma.latchConstant / outerRadius (m + 1) ^ n := by
  have h := Inner.derivative_comp_linear_le
    (Inner.taskProjection (Y := Leaf.Space Y E (m + 1)) (E := E) 8 (depth (m + 1)) (Fin.last 7))
    (Inner.taskProjection_norm_le _ _ _) (Inner.completion_contDiff (d.outerDirections (Fin.last 7))) hn Z
  apply h.trans
  have hp := LatchDerivativeSums.port_derivative_bound (depth (m + 1) + 1)
    (d.outerDirections (Fin.last 7)) (Inner.radius (depth (m + 1))) (Inner.radius_pos _ _) hv hn
    (Inner.taskProjection (Y := Leaf.Space Y E (m + 1)) (E := E) 8 (depth (m + 1)) (Fin.last 7) Z)
  apply hp.trans
  rw [Inner.radius_last]
  exact div_le_div_of_nonneg_right (LatchLemma.latchConstant_bounds hn).2.1
    (pow_nonneg (Inner.lastRadius_ge_one _ |>.trans' zero_le_one) n)

end GradientHessian.FirstHeight
