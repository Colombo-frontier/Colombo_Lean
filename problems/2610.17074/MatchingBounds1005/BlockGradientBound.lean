import MatchingBounds1005.BlockGradient
import Mathlib.Analysis.Calculus.Gradient.Basic

/-! Euclidean block geometry and gradient estimates for the actual objective. -/
noncomputable section
open scoped InnerProductSpace BigOperators

namespace MatchingBounds1005.BlockGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (G : BlockGeometry E)

abbrev BlockSpace (n : ℕ) := PiLp 2 (fun _ : Fin (n + 1) => E)

def euclideanObjective (r : ℝ) (n : ℕ) (z : BlockSpace (E := E) n) : ℝ :=
  G.objective r n (fun i => z i)

def euclideanGradient (r : ℝ) (n : ℕ) (z : BlockSpace (E := E) n) : BlockSpace (E := E) n :=
  (WithLp.equiv 2 (Fin (n + 1) → E)).symm (G.objectiveGradient r n (fun i => z i))

theorem objectiveDerivative_apply (r : ℝ) (n : ℕ) (z v : Fin (n + 1) → E) :
    G.objectiveDerivative r n z v = ∑ i, ⟪G.objectiveGradient r n z i, v i⟫_ℝ := by
  calc
    _ = G.objectiveDerivative r n z (∑ i, Pi.single i (v i)) := by
      rw [Finset.univ_sum_single]
    _ = ∑ i, G.objectiveDerivative r n z (Pi.single i (v i)) := map_sum _ _ _
    _ = _ := Finset.sum_congr rfl (fun i _ => G.objectiveDerivative_single r n z i (v i))

theorem euclideanObjective_hasFDerivAt (r : ℝ) (n : ℕ) (z : BlockSpace (E := E) n) :
    HasFDerivAt (G.euclideanObjective r n) (innerSL ℝ (G.euclideanGradient r n z)) z := by
  have h := (G.objective_hasFDerivAt r n (fun i => z i)).comp z
    (PiLp.hasFDerivAt_equiv (𝕜 := ℝ) 2 z)
  convert h using 1
  ext v
  change ⟪G.euclideanGradient r n z, v⟫_ℝ =
    G.objectiveDerivative r n (fun i => z i) (fun i => v i)
  rw [G.objectiveDerivative_apply]
  rfl

theorem euclideanObjective_hasGradientAt (r : ℝ) (n : ℕ) (z : BlockSpace (E := E) n) :
    HasGradientAt (G.euclideanObjective r n) (G.euclideanGradient r n z) z := by
  rw [hasGradientAt_iff_hasFDerivAt]
  convert G.euclideanObjective_hasFDerivAt r n z using 1

theorem euclideanObjective_gradient (r : ℝ) (n : ℕ) (z : BlockSpace (E := E) n) :
    gradient (G.euclideanObjective r n) z = G.euclideanGradient r n z :=
  (G.euclideanObjective_hasGradientAt r n z).gradient

def scalarReadout {n : ℕ} (z : Fin (n + 1) → E) : ℕ → ℝ
  | 0 => 1
  | k + 1 => if h : k < n + 1 then ⟪G.a, z ⟨k, h⟩⟫_ℝ else 0

@[simp] theorem scalarReadout_zero {n : ℕ} (z : Fin (n + 1) → E) :
    G.scalarReadout z 0 = 1 := rfl

@[simp] theorem scalarReadout_block {n : ℕ} (z : Fin (n + 1) → E) (i : Fin (n + 1)) :
    G.scalarReadout z (i.val + 1) = ⟪G.a, z i⟫_ℝ := by simp [scalarReadout, i.isLt]

@[simp] theorem scalarReadout_end {n : ℕ} (z : Fin (n + 1) → E) :
    G.scalarReadout z (n + 2) = 0 := by simp [scalarReadout]

theorem incomingReadout_eq_scalar {n : ℕ} (z : Fin (n + 1) → E) (i : Fin (n + 1)) :
    G.incomingReadout z i = G.scalarReadout z i.val := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · rw [G.incomingReadout_succ]
    simpa using (G.scalarReadout_block z j.castSucc).symm

def residualVector (r : ℝ) (n : ℕ) (z : Fin (n + 1) → E) : EuclideanSpace ℝ (Fin (n + 1)) :=
  (WithLp.equiv 2 _).symm (fun i => scalarResidual (Primitive.slope r) (G.scalarReadout z) (i.val + 1))

def contraction {n : ℕ} (w : E) (g : BlockSpace (E := E) n) : EuclideanSpace ℝ (Fin (n + 1)) :=
  (WithLp.equiv 2 _).symm (fun i => ⟪w, g i⟫_ℝ)

def forwardShift {n : ℕ} (g : BlockSpace (E := E) n) : BlockSpace (E := E) n :=
  (WithLp.equiv 2 _).symm (fun i => if h : i.val < n then g ⟨i.val + 1, by omega⟩ else 0)

@[simp] theorem forwardShift_castSucc {n : ℕ} (g : BlockSpace (E := E) n) (i : Fin n) :
    forwardShift g i.castSucc = g i.succ := by
  simp [forwardShift, i.isLt]
  rfl

@[simp] theorem forwardShift_last {n : ℕ} (g : BlockSpace (E := E) n) :
    forwardShift g (Fin.last n) = 0 := by simp [forwardShift]

theorem norm_contraction_le {n : ℕ} (w : E) (g : BlockSpace (E := E) n) :
    ‖contraction w g‖ ≤ ‖w‖ * ‖g‖ := by
  have hs : ‖contraction w g‖ ^ 2 ≤ (‖w‖ * ‖g‖) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, mul_pow, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    change ‖⟪w, g i⟫_ℝ‖ ^ 2 ≤ ‖w‖ ^ 2 * ‖g i‖ ^ 2
    have h := (sq_le_sq₀ (abs_nonneg ⟪w, g i⟫_ℝ)
      (mul_nonneg (norm_nonneg w) (norm_nonneg (g i)))).2 (abs_real_inner_le_norm w (g i))
    simpa [Real.norm_eq_abs, mul_pow] using h
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).1 hs

theorem norm_forwardShift_le {n : ℕ} (g : BlockSpace (E := E) n) :
    ‖forwardShift g‖ ≤ ‖g‖ := by
  have hs : ‖forwardShift g‖ ^ 2 ≤ ‖g‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_castSucc]
    simp only [forwardShift_castSucc, forwardShift_last, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, add_zero]
    rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succ]
    exact le_add_of_nonneg_left (sq_nonneg ‖g 0‖)
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hs

/-- Actual vector residual identity, with the terminal correction canceled only
under the zero-tail hypothesis. -/
theorem residualVector_identity (r : ℝ) (n : ℕ) (z : BlockSpace (E := E) n)
    (htail : ⟪G.a, z (Fin.last n)⟫_ℝ = 0) :
    G.tau • G.residualVector r n (fun i => z i) =
      contraction G.wOut (G.euclideanGradient r n z) +
        G.lam • contraction G.wIn (forwardShift (G.euclideanGradient r n z)) := by
  ext i
  change G.tau * scalarResidual (Primitive.slope r) (G.scalarReadout (fun j => z j)) (i.val + 1) =
    ⟪G.wOut, G.euclideanGradient r n z i⟫_ℝ +
      G.lam * ⟪G.wIn, forwardShift (G.euclideanGradient r n z) i⟫_ℝ
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [forwardShift_last, inner_zero_right, mul_zero, add_zero]
    change _ = ⟪G.wOut, G.gradientBlock (Primitive.slope r)
      (G.incomingReadout (fun j => z j) (Fin.last n)) (z (Fin.last n))
      (G.outgoingEntry (fun j => z j) (Fin.last n))⟫_ℝ
    rw [G.outgoingEntry_last, G.terminal_zero_readout _ _ _ htail]
    rw [G.incomingReadout_eq_scalar]
    have hlast := G.scalarReadout_block (fun j => z j) (Fin.last n)
    simp only [Fin.val_last] at hlast
    simp only [scalarResidual, Fin.val_last, hlast, htail,
      Nat.add_sub_cancel, scalarReadout_end, mul_zero, zero_sub, sub_zero]
  · rw [forwardShift_castSucc]
    change _ = ⟪G.wOut, G.gradientBlock (Primitive.slope r)
      (G.incomingReadout (fun k => z k) j.castSucc) (z j.castSucc)
      (G.outgoingEntry (fun k => z k) j.castSucc)⟫_ℝ +
      G.lam * ⟪G.wIn, G.gradientBlock (Primitive.slope r)
      (G.incomingReadout (fun k => z k) j.succ) (z j.succ)
      (G.outgoingEntry (fun k => z k) j.succ)⟫_ℝ
    rw [G.outgoingEntry_castSucc, G.incomingReadout_succ, G.residual_identity,
      G.incomingReadout_eq_scalar]
    have hcur := G.scalarReadout_block (fun k => z k) j.castSucc
    have hnext := G.scalarReadout_block (fun k => z k) j.succ
    simp only [Fin.coe_castSucc, Fin.val_succ] at hcur hnext
    simp only [scalarResidual, Fin.coe_castSucc, Nat.add_sub_cancel, hcur, hnext]

theorem residualVector_norm_lower (r : ℝ) (hr : 1 ≤ r) (n : ℕ) (z : Fin (n + 1) → E)
    (htail : ⟪G.a, z (Fin.last n)⟫_ℝ = 0) :
    (1 / 4 : ℝ) ≤ ‖G.residualVector r n z‖ := by
  have hlast := G.scalarReadout_block z (Fin.last n)
  simp only [Fin.val_last, htail] at hlast
  have h := Primitive.scalar_transition_norm r hr (n + 1) (by omega) (G.scalarReadout z)
    rfl (G.scalarReadout_end z) (by rw [hlast]; norm_num)
  rw [Primitive.potential_deriv] at h
  have hsets : Finset.Icc 1 (n + 1) = Finset.Ico 1 (n + 2) := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hsets, Finset.sum_Ico_eq_sum_range] at h
  simp only [PiLp.norm_eq_of_L2, residualVector, WithLp.equiv_symm_pi_apply,
    Real.norm_eq_abs, sq_abs]
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ => scalarResidual (Primitive.slope r) (G.scalarReadout z) (k + 1) ^ 2) (n + 1)]
  simpa [Nat.add_comm] using h

/-- Finite ℓ² triangle inequality and the two explicit contraction estimates. -/
theorem residualVector_norm_upper (r : ℝ) (n : ℕ) (z : BlockSpace (E := E) n)
    (htail : ⟪G.a, z (Fin.last n)⟫_ℝ = 0) :
    G.tau * ‖G.residualVector r n (fun i => z i)‖ ≤
      (‖G.wOut‖ + G.lam * ‖G.wIn‖) * ‖G.euclideanGradient r n z‖ := by
  have hn := congrArg norm (G.residualVector_identity r n z htail)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg G.tau_nonneg] at hn
  calc
    _ = _ := hn
    _ ≤ ‖contraction G.wOut (G.euclideanGradient r n z)‖ +
        ‖G.lam • contraction G.wIn (forwardShift (G.euclideanGradient r n z))‖ := norm_add_le _ _
    _ = ‖contraction G.wOut (G.euclideanGradient r n z)‖ +
        G.lam * ‖contraction G.wIn (forwardShift (G.euclideanGradient r n z))‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg G.lam_nonneg]
    _ ≤ ‖G.wOut‖ * ‖G.euclideanGradient r n z‖ +
        G.lam * (‖G.wIn‖ * ‖forwardShift (G.euclideanGradient r n z)‖) :=
      add_le_add (norm_contraction_le _ _)
        (mul_le_mul_of_nonneg_left (norm_contraction_le _ _) G.lam_nonneg)
    _ ≤ ‖G.wOut‖ * ‖G.euclideanGradient r n z‖ +
        G.lam * (‖G.wIn‖ * ‖G.euclideanGradient r n z‖) :=
      add_le_add_left (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (norm_forwardShift_le _) (norm_nonneg _)) G.lam_nonneg) _
    _ = _ := by ring

theorem block_gradient_certificate_contractions (r : ℝ) (hr : 1 ≤ r) (n : ℕ)
    (z : BlockSpace (E := E) n) (htail : ⟪G.a, z (Fin.last n)⟫_ℝ = 0) :
    G.tau / 4 ≤ (‖G.wOut‖ + G.lam * ‖G.wIn‖) * ‖gradient (G.euclideanObjective r n) z‖ := by
  rw [G.euclideanObjective_gradient]
  have hl := mul_le_mul_of_nonneg_left
    (G.residualVector_norm_lower r hr n (fun i => z i) htail) G.tau_nonneg
  have hu := G.residualVector_norm_upper r n z htail
  linarith

/-- Convert coercivity into the coefficient in the manuscript's certificate. -/
theorem contraction_coefficient_bound (γ : ℝ) (hγ : 0 < γ)
    (hcoercive : ∀ x, γ * ‖x‖ ^ 2 ≤ ⟪x, G.H x⟫_ℝ) :
    G.beta * Real.sqrt γ * (‖G.wOut‖ + G.lam * ‖G.wIn‖) ≤
      Real.sqrt G.beta + G.beta * Real.sqrt G.rho / G.alpha := by
  have hb : 0 < G.beta := G.beta_pos
  have ha : 0 < G.alpha := G.alpha_pos
  have hout : G.beta * Real.sqrt γ * ‖G.wOut‖ ≤ Real.sqrt G.beta := by
    apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hb.le]
    calc
      _ = G.beta ^ 2 * (γ * ‖G.wOut‖ ^ 2) := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hγ.le]
        ring
      _ ≤ G.beta ^ 2 * G.tau :=
        mul_le_mul_of_nonneg_left (G.wOut_coercive_bound γ hcoercive) (sq_nonneg _)
      _ = G.beta := by
        simp [tau, pow_two, mul_assoc, G.beta_ne]
  have hin : Real.sqrt γ * ‖G.wIn‖ ≤ Real.sqrt G.rho := by
    apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
    rw [mul_pow, Real.sq_sqrt hγ.le, Real.sq_sqrt G.rho_nonneg]
    exact G.wIn_coercive_bound γ hcoercive
  calc
    _ = G.beta * Real.sqrt γ * ‖G.wOut‖ +
      (G.beta * G.lam) * (Real.sqrt γ * ‖G.wIn‖) := by ring
    _ ≤ Real.sqrt G.beta + (G.beta * G.lam) * Real.sqrt G.rho :=
      add_le_add hout (mul_le_mul_of_nonneg_left hin (mul_nonneg hb.le G.lam_nonneg))
    _ = _ := by simp only [lam, div_eq_mul_inv]; ring

/-- `ana:eq:block-cert`, for the actual smooth objective and its actual
Euclidean gradient. There are `n+1` blocks. Coercivity is `H ⪰ γ I`.
The terminal hypothesis is exactly zero readout, not an omitted boundary term. -/
theorem block_gradient_certificate (r : ℝ) (hr : 1 ≤ r) (n : ℕ)
    (z : BlockSpace (E := E) n) (htail : ⟪G.a, z (Fin.last n)⟫_ℝ = 0)
    (γ : ℝ) (hγ : 0 < γ)
    (hcoercive : ∀ x, γ * ‖x‖ ^ 2 ≤ ⟪x, G.H x⟫_ℝ) :
    Real.sqrt γ / (4 * (Real.sqrt G.beta + G.beta * Real.sqrt G.rho / G.alpha)) ≤
      ‖gradient (G.euclideanObjective r n) z‖ := by
  have hb : 0 < G.beta := G.beta_pos
  have ha : 0 < G.alpha := G.alpha_pos
  have hbase := G.block_gradient_certificate_contractions r hr n z htail
  have hcoef := G.contraction_coefficient_bound γ hγ hcoercive
  have hbt : G.beta * G.tau = 1 := mul_inv_cancel₀ G.beta_ne
  have hscale : 0 ≤ G.beta * Real.sqrt γ := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hbase hscale
  have hn := mul_le_mul_of_nonneg_right hcoef (norm_nonneg (gradient (G.euclideanObjective r n) z))
  have hleft : G.beta * Real.sqrt γ * (G.tau / 4) = Real.sqrt γ / 4 := by
    calc
      _ = (G.beta * G.tau) * Real.sqrt γ / 4 := by ring
      _ = _ := by rw [hbt, one_mul]
  rw [hleft] at hscaled
  have hbound : Real.sqrt γ / 4 ≤
      (Real.sqrt G.beta + G.beta * Real.sqrt G.rho / G.alpha) *
        ‖gradient (G.euclideanObjective r n) z‖ := by
    nlinarith only [hscaled, hn]
  have hden : 0 < 4 * (Real.sqrt G.beta + G.beta * Real.sqrt G.rho / G.alpha) := by
    have hs : 0 < Real.sqrt G.beta := Real.sqrt_pos.2 hb
    have hp : 0 ≤ G.beta * Real.sqrt G.rho / G.alpha := by positivity
    linarith
  apply (div_le_iff₀ hden).mpr
  nlinarith only [hbound]

end MatchingBounds1005.BlockGeometry
