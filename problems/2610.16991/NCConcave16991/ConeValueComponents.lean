import NCConcave16991.ConeValueBall

/-!
# Literal cone components and their exact constrained primal value

The dual variable uses the genuine Hilbert L2 block norm. The hidden mean is
computed from the component rows. No dual maximization or value identity is
an input hypothesis.
-/

noncomputable section

open Set Metric
open scoped BigOperators InnerProductSpace

namespace NCConcave16991.ConeValue

open ConeClockGap ConeRadial

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n M : ℕ}

abbrev Blocks (E : Type*) (M : ℕ) := PiLp 2 (fun _ : Fin (M + 1) ↦ E)
abbrev PrimalBlocks (E : Type*) (M : ℕ) := WithLp 2 (Blocks E M × Blocks E M)
abbrev JointBlocks (E : Type*) (M : ℕ) := WithLp 2 (PrimalBlocks E M × Blocks E M)

def residual (q : ℝ) (v : Fin (M + 1) → E) (z u : Blocks E M) : Blocks E M :=
  WithLp.toLp 2 (fun j ↦ previousGate q v (fun j ↦ u j) j • (zeta (z j) - v j))

def clockGuard (q : ℝ) (v : Fin (M + 1) → E) (z u : Blocks E M) : ℝ :=
  ∑ j, (clock q (v j) (z j) (u j) + ConeRadial.guard 3000 (z j))

/-- The literal component function (D.5), including its selected hidden row. -/
def component (R q : ℝ) (w : Fin n → Fin (M + 1) → E) (i : Fin n)
    (z u y : Blocks E M) : ℝ :=
  clockGuard q (sourceMean w) z u + R⁻¹ * ∑ j,
    previousGate q (sourceMean w) (fun j ↦ u j) j *
      ⟪zeta (z j) - Real.sqrt (n : ℝ) • w i j, y j⟫_ℝ

/-- The actual same component on its joint primal-dual Hilbert product. -/
def jointComponent (R q : ℝ) (w : Fin n → Fin (M + 1) → E) (i : Fin n)
    (x : JointBlocks E M) : ℝ := component R q w i x.fst.fst x.fst.snd x.snd

/-- The finite average written in its actual unit-ball dual multiplier. -/
def branch (q : ℝ) (v : Fin (M + 1) → E) (z u a : Blocks E M) : ℝ :=
  clockGuard q v z u + ⟪residual q v z u, a⟫_ℝ

theorem residual_norm (q : ℝ) (v : Fin (M + 1) → E) (z u : Blocks E M) :
    ‖residual q v z u‖ = Real.sqrt (∑ j,
      (previousGate q v (fun j ↦ u j) j) ^ 2 * ‖zeta (z j) - v j‖ ^ 2) := by
  apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (by positivity), PiLp.norm_sq_eq_of_L2]
  simp only [residual, PiLp.toLp_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

theorem component_average (hn : 0 < n) (R q : ℝ)
    (w : Fin n → Fin (M + 1) → E) (z u y : Blocks E M) :
    (n : ℝ)⁻¹ * ∑ i, component R q w i z u y =
      clockGuard q (sourceMean w) z u + R⁻¹ * ⟪residual q (sourceMean w) z u, y⟫_ℝ := by
  have hnr : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hinner (j : Fin (M + 1)) :
      (n : ℝ)⁻¹ * ∑ i, ⟪zeta (z j) - Real.sqrt (n : ℝ) • w i j, y j⟫_ℝ =
      ⟪zeta (z j) - sourceMean w j, y j⟫_ℝ := by
    have hvec : (n : ℝ)⁻¹ • ∑ i, (zeta (z j) - Real.sqrt (n : ℝ) • w i j) =
        zeta (z j) - sourceMean w j := by
      rw [Finset.sum_sub_distrib, smul_sub, average_scaled_row hn w j]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hnr, one_smul]
    calc
      _ = ⟪(n : ℝ)⁻¹ • ∑ i, (zeta (z j) - Real.sqrt (n : ℝ) • w i j), y j⟫_ℝ := by
        rw [real_inner_smul_left, sum_inner]
      _ = _ := by rw [hvec]
  have hsource : (n : ℝ)⁻¹ * (∑ i, ∑ j,
      previousGate q (sourceMean w) (fun j ↦ u j) j *
        ⟪zeta (z j) - Real.sqrt (n : ℝ) • w i j, y j⟫_ℝ) =
      ⟪residual q (sourceMean w) z u, y⟫_ℝ := by
    calc
      _ = ∑ j, previousGate q (sourceMean w) (fun j ↦ u j) j *
          ((n : ℝ)⁻¹ * ∑ i, ⟪zeta (z j) - Real.sqrt (n : ℝ) • w i j, y j⟫_ℝ) := by
        rw [Finset.sum_comm, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [← Finset.mul_sum]
        ring
      _ = ∑ j, previousGate q (sourceMean w) (fun j ↦ u j) j *
          ⟪zeta (z j) - sourceMean w j, y j⟫_ℝ := by simp_rw [hinner]
      _ = _ := by simp only [residual, PiLp.inner_apply, PiLp.toLp_apply, real_inner_smul_left]
  unfold component
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum]
  calc
    (n : ℝ)⁻¹ * ((n : ℝ) * clockGuard q (sourceMean w) z u +
        R⁻¹ * ∑ i, ∑ j, previousGate q (sourceMean w) (fun j ↦ u j) j *
          ⟪zeta (z j) - Real.sqrt (n : ℝ) • w i j, y j⟫_ℝ) =
      clockGuard q (sourceMean w) z u + R⁻¹ * ((n : ℝ)⁻¹ * ∑ i, ∑ j,
        previousGate q (sourceMean w) (fun j ↦ u j) j *
          ⟪zeta (z j) - Real.sqrt (n : ℝ) • w i j, y j⟫_ℝ) := by
        field_simp [hnr]
    _ = _ := by rw [hsource]

theorem component_average_eq_branch (hn : 0 < n) (R q : ℝ)
    (w : Fin n → Fin (M + 1) → E) (z u y : Blocks E M) :
    (n : ℝ)⁻¹ * ∑ i, component R q w i z u y =
      branch q (sourceMean w) z u (R⁻¹ • y) := by
  rw [component_average hn, branch, real_inner_smul_right]

theorem branch_sum (q : ℝ) (v : Fin (M + 1) → E) (z u a : Blocks E M) :
    branch q v z u a = ∑ j, (clock q (v j) (z j) (u j) + ConeRadial.guard 3000 (z j) +
      previousGate q v (fun j ↦ u j) j * ⟪zeta (z j) - v j, a j⟫_ℝ) := by
  simp only [branch, clockGuard, residual, PiLp.inner_apply, real_inner_smul_left]
  exact (Finset.sum_add_distrib).symm

/-- The actual supremum of the actual finite average on the specified closed dual ball. -/
def dualValue (R q : ℝ) (w : Fin n → Fin (M + 1) → E) (z u : Blocks E M) : ℝ :=
  sSup ((fun y : Blocks E M ↦ (n : ℝ)⁻¹ * ∑ i, component R q w i z u y) '' closedBall 0 R)

theorem dualValue_eq_value (hn : 0 < n) {R : ℝ} (hR : 0 < R) (q : ℝ)
    (w : Fin n → Fin (M + 1) → E) (z u : Blocks E M) :
    dualValue R q w z u = ConeClockGap.value q (sourceMean w) (fun j ↦ z j) (fun j ↦ u j) := by
  unfold dualValue
  simp_rw [component_average hn]
  rw [ball_affine_sSup hR]
  rw [ConeClockGap.value, ← residual_norm]
  rfl

def primalValue (R q : ℝ) (w : Fin n → Fin (M + 1) → E) (x : PrimalBlocks E M) : ℝ :=
  dualValue R q w x.fst x.snd

theorem primalValue_zero (hn : 0 < n) {R q : ℝ} (hR : 0 < R) (hq : 0 < q)
    (w : Fin n → Fin (M + 1) → E) (hw : ∀ j, Orthonormal ℝ (fun i ↦ w i j)) :
    primalValue R q w (0 : PrimalBlocks E M) = 1 := by
  rw [primalValue, dualValue_eq_value hn hR]
  exact ConeClockGap.value_zero hq (sourceMean w) (sourceMean_unit hn w hw)

theorem primalValue_lower (hn : 0 < n) {R q : ℝ} (hR : 0 < R) (hq : 1 ≤ q)
    (w : Fin n → Fin (M + 1) → E) (hw : ∀ j, Orthonormal ℝ (fun i ↦ w i j))
    (x : PrimalBlocks E M) :
    -91 * (M + 1 : ℕ) * q ≤ primalValue R q w x := by
  rw [primalValue, dualValue_eq_value hn hR]
  exact ConeClockGap.value_lower_bound hq (sourceMean w) (sourceMean_unit hn w hw) _ _

theorem primalValue_initial_gap (hn : 0 < n) {R q : ℝ} (hR : 0 < R) (hq : 1 ≤ q)
    (w : Fin n → Fin (M + 1) → E) (hw : ∀ j, Orthonormal ℝ (fun i ↦ w i j)) :
    primalValue R q w (0 : PrimalBlocks E M) - sInf (range (primalValue R q w)) ≤
      1 + 91 * (M + 1 : ℕ) * q := by
  rw [primalValue_zero hn hR (by linarith) w hw]
  have hl : -91 * (M + 1 : ℕ) * q ≤ sInf (range (primalValue R q w)) := by
    apply le_csInf (range_nonempty _)
    rintro a ⟨x, rfl⟩
    exact primalValue_lower hn hR hq w hw x
  linarith

end NCConcave16991.ConeValue
