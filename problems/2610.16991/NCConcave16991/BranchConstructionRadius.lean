import NCConcave16991.BranchConstructionPortEnergy
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # The actual square-root-in-n dual-radius scale of the branch pipe -/

namespace NCConcave16991.BranchConstruction

noncomputable section

open scoped InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048
set_option maxSynthPendingDepth 4

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {m : ℕ} (V : Fin ((m + 1) + 1) → Type*)
  [∀ j, NormedAddCommGroup (V j)] [∀ j, InnerProductSpace ℝ (V j)]
  [∀ j, CompleteSpace (V j)] [∀ j, FiniteDimensional ℝ (V j)]
  (B : ∀ t : Fin (m + 1), BranchGeometry.BranchFamily (ι := ι) (V t.castSucc) (V t.succ))

theorem portInverseEnergy_upper (a : V 0) (b : V (Fin.last (m + 1))) :
    portInverseEnergy V B a b ≤ EndpointConstants.endpointK m * (EndpointConstants.endpointC m + 1) *
      (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  have hk : 0 < EndpointConstants.endpointK m := by
    have hh := EndpointConstants.endpointK_lower m
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hg := terminalGreenOperator_upper V B b
  have hc := BranchGeometry.abs_inner_le_half_norm_sq b (terminalTransport V B a)
  rw [(terminalTransport V B).norm_map] at hc
  have hscaled := mul_le_mul_of_nonneg_left (abs_le.mp hc).1 (by positivity : 0 ≤ 2 * EndpointConstants.endpointK m)
  rw [portInverseEnergy_formula]
  nlinarith only [hg, hscaled]

theorem portInverseEnergy_upper_three (a : V 0) (b : V (Fin.last (m + 1))) :
    portInverseEnergy V B a b ≤ 3 * EndpointConstants.endpointK m * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  have hk : 0 < EndpointConstants.endpointK m := by
    have hh := EndpointConstants.endpointK_lower m
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hc : EndpointConstants.endpointC m + 1 ≤ 3 := by
    have hh := EndpointConstants.endpointC_upper m
    have hc1 := EndpointConstants.cosh_one_lt_eight_fifths
    linarith
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc hk.le)
    (add_nonneg (sq_nonneg ‖a‖) (sq_nonneg ‖b‖))
  exact (portInverseEnergy_upper V B a b).trans (by nlinarith only [hh])

def paperOptimizer (a : V 0) (b : V (Fin.last (m + 1))) : Layers V :=
  optimizer V B (1 / ((m : ℝ) + 2) ^ 2) (by positivity) (BranchGeometry.beta ι)
    (Real.sqrt (BranchGeometry.beta ι / EndpointConstants.endpointK m)) (portSource V a b)

theorem paperOptimizer_norm_sq_bound (a : V 0) (b : V (Fin.last (m + 1))) :
    ‖paperOptimizer V B a b‖ ^ 2 ≤
      (3 * ((m : ℝ) + 2) ^ 2 / BranchGeometry.beta ι) * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  let μ : ℝ := 1 / ((m : ℝ) + 2) ^ 2
  have hμ : 0 < μ := by dsimp [μ]; positivity
  let β : ℝ := BranchGeometry.beta ι
  let k : ℝ := EndpointConstants.endpointK m
  have hβ : 0 < β := BranchGeometry.beta_pos ι
  have hk : 0 < k := by
    have hh := EndpointConstants.endpointK_lower m
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    dsimp [k]
    linarith
  have hN : 0 < ((m : ℝ) + 2) ^ 2 := by positivity
  have hi := inverse_energy_bound V B μ hμ (portSource V a b)
  have hid : ‖inverse V B μ hμ (portSource V a b)‖ ^ 2 ≤
      ((m : ℝ) + 2) ^ 2 * portInverseEnergy V B a b := by
    have hh : ‖inverse V B μ hμ (portSource V a b)‖ ^ 2 / ((m : ℝ) + 2) ^ 2 ≤ portInverseEnergy V B a b := by
      simpa [μ, portInverseEnergy, div_eq_mul_inv, mul_comm] using hi
    have hh' := (div_le_iff₀ hN).mp hh
    nlinarith only [hh']
  have he := mul_le_mul_of_nonneg_left (portInverseEnergy_upper_three V B a b) hN.le
  have hcoef : (Real.sqrt (β / k) / β) ^ 2 = 1 / (β * k) := by
    rw [div_pow, Real.sq_sqrt (div_nonneg hβ.le hk.le)]
    field_simp [hβ.ne', hk.ne']
  change (‖(Real.sqrt (β / k) / β) • inverse V B μ hμ (portSource V a b)‖) ^ 2 ≤ _
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hcoef]
  have hh := mul_le_mul_of_nonneg_left (hid.trans he) (by positivity : 0 ≤ 1 / (β * k))
  have halg : (1 / (β * k)) * (((m : ℝ) + 2) ^ 2 * (3 * EndpointConstants.endpointK m *
      (‖a‖ ^ 2 + ‖b‖ ^ 2))) = (3 * ((m : ℝ) + 2) ^ 2 / β) * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
    dsimp [k]
    have hK : EndpointConstants.endpointK m ≠ 0 := hk.ne'
    field_simp [hβ.ne', hK]
  rw [halg] at hh
  exact hh

theorem sqrt_sqrt_card : Real.sqrt (Real.sqrt (Fintype.card ι : ℝ)) = (Fintype.card ι : ℝ) ^ (1 / 4 : ℝ) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg (Fintype.card ι))]
  norm_num

/-- The source's actual unconstrained dual maximizer has radius
sqrt(3)*N*n^(1/4) times the Euclidean connector norm. -/
theorem paperOptimizer_norm_bound (a : V 0) (b : V (Fin.last (m + 1))) :
    ‖paperOptimizer V B a b‖ ≤ Real.sqrt 3 * ((m : ℝ) + 2) * (Fintype.card ι : ℝ) ^ (1 / 4 : ℝ) *
      Real.sqrt (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  have hs : ‖paperOptimizer V B a b‖ ^ 2 ≤
      3 * ((m : ℝ) + 2) ^ 2 * Real.sqrt (Fintype.card ι) * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
    simpa [BranchGeometry.beta, div_eq_mul_inv] using paperOptimizer_norm_sq_bound V B a b
  have hq : ((Fintype.card ι : ℝ) ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt (Fintype.card ι) := by
    rw [← sqrt_sqrt_card, Real.sq_sqrt (Real.sqrt_nonneg _)]
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  simp only [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), hq,
    Real.sq_sqrt (add_nonneg (sq_nonneg ‖a‖) (sq_nonneg ‖b‖))]
  nlinarith only [hs]

end

end NCConcave16991.BranchConstruction
