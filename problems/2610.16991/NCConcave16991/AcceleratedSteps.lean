import NCConcave16991.AcceleratedModel
import NCConcave16991.AcceleratedWeights
import Mathlib.Tactic.Module

/-! # Actual accelerated dual extrapolation and its deterministic potential step -/

noncomputable section

open Set
open scoped InnerProductSpace BigOperators

namespace NCConcave16991.Accelerated

variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

structure State (X Y : Type*) where
  y : Y
  z : Y
  primalSum : X

/-- The extrapolation can lie outside the feasible dual set. -/
def center (τ : ℝ) (k : ℕ) (s : State X Y) : Y :=
  (mass τ (k + 1))⁻¹ • (mass τ k • s.y + weight τ k • s.z)

/-- One actual accelerated step after calling the prox saddle solver at the extrapolated center. -/
def advance (τ : ℝ) (solve : ℕ → Y → ProxResult (X := X) (Y := Y)) (k : ℕ)
    (s : State X Y) : State X Y :=
  let v := center τ k s
  let r := solve k v
  let g := τ • (v - r.y)
  ⟨r.y, s.z - weight τ k • g, s.primalSum + weight τ k • r.x⟩

/-- The actual accelerated trajectory, initialized with zero primal mass. -/
def states (τ : ℝ) (solve : ℕ → Y → ProxResult (X := X) (Y := Y)) (y0 : Y) : ℕ → State X Y
  | 0 => ⟨y0, y0, 0⟩
  | k + 1 => advance τ solve k (states τ solve y0 k)

def resultAt (τ : ℝ) (solve : ℕ → Y → ProxResult (X := X) (Y := Y)) (y0 : Y) (k : ℕ) :=
  solve k (center τ k (states τ solve y0 k))

def dualGradient (τ : ℝ) (solve : ℕ → Y → ProxResult (X := X) (Y := Y)) (y0 : Y) (k : ℕ) : Y :=
  τ • (center τ k (states τ solve y0 k) - (resultAt τ solve y0 k).y)

/-- The actual weighted primal output. -/
def primalOutput (τ : ℝ) (solve : ℕ → Y → ProxResult (X := X) (Y := Y)) (y0 : Y) (K : ℕ) : X :=
  (mass τ K)⁻¹ • (states τ solve y0 K).primalSum

 theorem states_y_succ (τ : ℝ) (solve : ℕ → Y → ProxResult (X := X) (Y := Y)) (y0 : Y) (k : ℕ) :
    (states τ solve y0 (k + 1)).y = (resultAt τ solve y0 k).y := rfl

 theorem states_z_succ (τ : ℝ) (solve : ℕ → Y → ProxResult (X := X) (Y := Y)) (y0 : Y) (k : ℕ) :
    (states τ solve y0 (k + 1)).z = (states τ solve y0 k).z - weight τ k • dualGradient τ solve y0 k := rfl

 theorem primalSum_eq (τ : ℝ) (solve : ℕ → Y → ProxResult (X := X) (Y := Y)) (y0 : Y) (K : ℕ) :
    (states τ solve y0 K).primalSum = ∑ k ∈ Finset.range K, weight τ k • (resultAt τ solve y0 k).x := by
  induction K with
  | zero => simp [states]
  | succ K ih => rw [Finset.sum_range_succ, ← ih]; rfl

 theorem center_identity {τ : ℝ} (hτ : 0 < τ) (k : ℕ) (s : State X Y) :
    mass τ (k + 1) • center τ k s = mass τ k • s.y + weight τ k • s.z := by
  rw [center, smul_smul, mul_inv_cancel₀ (mass_succ_pos hτ k).ne', one_smul]

/-- The key vector identity is proved for the actually defined extrapolation and update. -/
theorem extrapolation_identity {τ : ℝ} (hτ : 0 < τ)
    (solve : ℕ → Y → ProxResult (X := X) (Y := Y)) (y0 : Y) (k : ℕ) :
    mass τ k • ((resultAt τ solve y0 k).y - (states τ solve y0 k).y) =
      weight τ k • ((states τ solve y0 k).z - (resultAt τ solve y0 k).y) -
        (weight τ k) ^ 2 • dualGradient τ solve y0 k := by
  have hc := center_identity hτ k (states τ solve y0 k)
  have hg : (weight τ k) ^ 2 • dualGradient τ solve y0 k =
      mass τ (k + 1) • (center τ k (states τ solve y0 k) - (resultAt τ solve y0 k).y) := by
    dsimp only [dualGradient]
    rw [smul_smul]
    have hw : weight τ k ^ 2 * τ = mass τ (k + 1) := by nlinarith [weight_identity hτ k]
    rw [hw]
  rw [hg]
  simp only [smul_sub]
  rw [hc, mass_succ]
  module

/-- Pure Hilbert algebra behind the accelerated estimate sequence. -/
theorem potential_step {A a e Hnew Hold f : ℝ} (hA : 0 ≤ A) (ha : 0 ≤ a)
    (oldY newY oldZ g target : Y)
    (hid : A • (newY - oldY) = a • (oldZ - newY) - a ^ 2 • g)
    (hprev : Hnew + ⟪g, oldY - newY⟫_ℝ - e ≤ Hold)
    (htarget : Hnew + ⟪g, target - newY⟫_ℝ - e ≤ -f) :
    (A + a) * Hnew - A * Hold + ‖oldZ - a • g - target‖ ^ 2 / 2 - ‖oldZ - target‖ ^ 2 / 2 ≤
      -a * f + (A + a) * e := by
  have hi := congrArg (fun u : Y ↦ ⟪g, u⟫_ℝ) hid
  simp only [inner_smul_right, inner_sub_right, real_inner_self_eq_norm_sq] at hi
  have hp := mul_le_mul_of_nonneg_left hprev hA
  have ht := mul_le_mul_of_nonneg_left htarget ha
  have hdiff : oldZ - a • g - target = (oldZ - target) - a • g := by abel
  rw [hdiff, norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hcomm := real_inner_comm g (oldZ - target)
  rw [hcomm]
  simp only [inner_sub_right] at hp ht ⊢
  have hn := mul_nonneg (sq_nonneg a) (sq_nonneg ‖g‖)
  nlinarith

/-- The actual residual checks imply the accelerated one-step estimate. -/
theorem checked_potential_step (F : CompactSaddle X Y) {τ ζ DX DY : ℝ} (hτ : 0 < τ)
    (hDX : ∀ x ∈ F.primal, ∀ u ∈ F.primal, ‖x - u‖ ≤ DX)
    (hDY : ∀ y ∈ F.dual, ∀ w ∈ F.dual, ‖y - w‖ ≤ DY)
    (solve : ℕ → Y → ProxResult (X := X) (Y := Y)) (y0 : Y) (k : ℕ)
    (hcheck : ResidualCheck F τ ζ (center τ k (states τ solve y0 k)) (resultAt τ solve y0 k))
    (hprevious : (states τ solve y0 k).y ∈ F.dual) {target : Y} (htarget : target ∈ F.dual) :
    mass τ (k + 1) * dualValue F (states τ solve y0 (k + 1)).y -
      mass τ k * dualValue F (states τ solve y0 k).y +
      ‖(states τ solve y0 (k + 1)).z - target‖ ^ 2 / 2 -
      ‖(states τ solve y0 k).z - target‖ ^ 2 / 2 ≤
      -weight τ k * F.objective (resultAt τ solve y0 k).x target +
        mass τ (k + 1) * ((DX + DY) * ζ) := by
  have hp := residual_dual_model F hDX hDY hcheck hprevious
  have ht := residual_affine_model F hDX hDY hcheck htarget
  have h := potential_step (mass_nonneg hτ k) (weight_pos hτ k).le
    (states τ solve y0 k).y (resultAt τ solve y0 k).y (states τ solve y0 k).z
    (dualGradient τ solve y0 k) target (extrapolation_identity hτ solve y0 k) hp ht
  simpa only [mass_succ, states_y_succ, states_z_succ] using h

end NCConcave16991.Accelerated



