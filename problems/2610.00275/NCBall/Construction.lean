import NCBall.Geometry
import NCBall.RadialBump
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! # The actual smooth localized function, (6.14) and (6.15)

This file constructs a smooth cutoff, defines the finite sum in the manuscript,
proves value locality, and proves that the terminal center is stationary.
No probabilistic law is imposed on the vectors `V` here.
-/

noncomputable section
open Set Metric Filter
open scoped BigOperators Topology InnerProductSpace ContDiff

namespace NCBall

/-- The fixed radial construction supplies dimension-independent constants. -/
def cutoff (n : ℕ) (x : Space n) : ℝ := radialCutoff x

theorem cutoff_smooth (n : ℕ) : ContDiff ℝ ∞ (cutoff n) := radialCutoff_smooth

theorem cutoff_range {n : ℕ} (x : Space n) :
    0 ≤ cutoff n x ∧ cutoff n x ≤ 1 :=
  radialCutoff_range x

theorem cutoff_one {n : ℕ} {x : Space n} (hx : ‖x‖ ≤ 1 / 4) :
    cutoff n x = 1 :=
  radialCutoff_one hx

theorem cutoff_zero {n : ℕ} {x : Space n} (hx : 1 ≤ ‖x‖) :
    cutoff n x = 0 :=
  radialCutoff_zero hx

def localBump {n : ℕ} (v y : Space n) : ℝ := cutoff n y * ⟪v, y⟫_ℝ

def terminalBump {n : ℕ} (y : Space n) : ℝ := cutoff n y * y 0

def chainValue {n : ℕ} (M : ℕ) (ρ γ lam : ℝ)
    (c V : ℕ → Space n) (x : Space n) : ℝ :=
  -γ * x 0 + lam * ρ * ∑ j ∈ Finset.range M, localBump (V j) (ρ⁻¹ • (x - c j)) +
    γ * ρ * terminalBump (ρ⁻¹ • (x - c M))

theorem localBump_smooth {n : ℕ} (v : Space n) : ContDiff ℝ ∞ (localBump v) := by
  exact (cutoff_smooth n).mul (contDiff_const.inner ℝ contDiff_id)

theorem terminalBump_smooth (n : ℕ) : ContDiff ℝ ∞ (@terminalBump n) := by
  exact (cutoff_smooth n).mul (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin (n + 1)) 0).contDiff

/-- Every fixed sample function is C∞ for the actual cutoff constructed above. -/
theorem chainValue_smooth {n : ℕ} (M : ℕ) (ρ γ lam : ℝ)
    (c V : ℕ → Space n) : ContDiff ℝ ∞ (chainValue M ρ γ lam c V) := by
  have hscale (j : ℕ) : ContDiff ℝ ∞ (fun x : Space n => ρ⁻¹ • (x - c j)) :=
    contDiff_const.smul (contDiff_id.sub contDiff_const)
  have hclock : ContDiff ℝ ∞ (fun x : Space n => -γ * x 0) :=
    contDiff_const.mul (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin (n + 1)) 0).contDiff
  exact (hclock.add (contDiff_const.mul (ContDiff.sum fun j _ =>
    (localBump_smooth (V j)).comp (hscale j)))).add
    (contDiff_const.mul ((terminalBump_smooth n).comp (hscale M)))

theorem scaled_norm {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ) (x c : Space n) :
    ‖ρ⁻¹ • (x - c)‖ = dist x c / ρ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ), dist_eq_norm]
  ring

theorem localBump_eq_zero_outside {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ)
    (x c v : Space n) (hx : ρ ≤ dist x c) :
    localBump v (ρ⁻¹ • (x - c)) = 0 := by
  have h : 1 ≤ ‖ρ⁻¹ • (x - c)‖ := by
    rw [scaled_norm hρ]
    exact (le_div_iff₀ hρ).2 (by simpa using hx)
  simp [localBump, cutoff_zero h]

theorem terminalBump_eq_zero_outside {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ)
    (x c : Space n) (hx : ρ ≤ dist x c) :
    terminalBump (ρ⁻¹ • (x - c)) = 0 := by
  have h : 1 ≤ ‖ρ⁻¹ • (x - c)‖ := by
    rw [scaled_norm hρ]
    exact (le_div_iff₀ hρ).2 (by simpa using hx)
  simp [terminalBump, cutoff_zero h]

/-- In a nonterminal room, the returned value has exactly one informative scalar.
The separation premises below will be discharged by `rooms_disjoint`. -/
theorem chainValue_one_measurement {n : ℕ} {M j : ℕ} (hj : j < M)
    {ρ γ lam : ℝ} (hρ : 0 < ρ) (c V : ℕ → Space n) (x : Space n)
    (hother : ∀ k < M, k ≠ j → ρ ≤ dist x (c k))
    (hterminal : ρ ≤ dist x (c M)) :
    chainValue M ρ γ lam c V x = -γ * x 0 +
      lam * ρ * ⟪V j, cutoff n (ρ⁻¹ • (x - c j)) • (ρ⁻¹ • (x - c j))⟫_ℝ := by
  have hs : ∑ k ∈ Finset.range M, localBump (V k) (ρ⁻¹ • (x - c k)) =
      localBump (V j) (ρ⁻¹ • (x - c j)) := by
    apply Finset.sum_eq_single j
    · intro k hk hkj
      exact localBump_eq_zero_outside hρ x (c k) (V k)
        (hother k (Finset.mem_range.mp hk) hkj)
    · simp [Finset.mem_range.mpr hj]
  rw [chainValue, hs, terminalBump_eq_zero_outside hρ x (c M) hterminal,
    mul_zero, add_zero, localBump, inner_smul_right]
  simp only [inner_smul_right]

theorem chainValue_outside {n : ℕ} {M : ℕ} {ρ γ lam : ℝ} (hρ : 0 < ρ)
    (c V : ℕ → Space n) (x : Space n)
    (hout : ∀ j ≤ M, ρ ≤ dist x (c j)) :
    chainValue M ρ γ lam c V x = -γ * x 0 := by
  have hs : ∑ j ∈ Finset.range M, localBump (V j) (ρ⁻¹ • (x - c j)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    exact localBump_eq_zero_outside hρ x (c j) (V j)
      (hout j (Nat.le_of_lt (Finset.mem_range.mp hj)))
  simp [chainValue, hs, terminalBump_eq_zero_outside hρ x (c M) (hout M le_rfl)]

/-- The entire inner terminal ball is flat, not just its center. -/
theorem chainValue_terminal_core {n : ℕ} {M : ℕ} {ρ γ lam : ℝ} (hρ : 0 < ρ)
    (U V : ℕ → Space n) (hU : ∀ i, U i 0 = 0) (x : Space n)
    (hx : dist x (roomCenter ρ U M) ≤ ρ / 4) :
    chainValue M ρ γ lam (roomCenter ρ U) V x = -γ * (roomCenter ρ U M) 0 := by
  have hm : x ∈ closedBall (roomCenter ρ U M) ρ := by
    rw [mem_closedBall]
    linarith
  have hs : ∑ j ∈ Finset.range M,
      localBump (V j) (ρ⁻¹ • (x - roomCenter ρ U j)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hnot : x ∉ closedBall (roomCenter ρ U j) ρ := by
      intro hjx
      exact Set.disjoint_left.mp
        (rooms_disjoint hρ U hU (Nat.ne_of_lt (Finset.mem_range.mp hj))) hjx hm
    exact localBump_eq_zero_outside hρ x (roomCenter ρ U j) (V j)
      (le_of_lt (by simpa only [mem_closedBall, not_le] using hnot))
  have hcut : cutoff n (ρ⁻¹ • (x - roomCenter ρ U M)) = 1 := by
    apply cutoff_one
    rw [scaled_norm hρ]
    apply (div_le_iff₀ hρ).2
    linarith
  simp only [chainValue, hs, mul_zero, add_zero, terminalBump, hcut, one_mul,
    PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  field_simp
  ring

theorem terminal_center_gradient_zero {n : ℕ} {M : ℕ} {ρ γ lam : ℝ} (hρ : 0 < ρ)
    (U V : ℕ → Space n) (hU : ∀ i, U i 0 = 0) :
    gradient (chainValue M ρ γ lam (roomCenter ρ U) V) (roomCenter ρ U M) = 0 := by
  have heq : chainValue M ρ γ lam (roomCenter ρ U) V =ᶠ[𝓝 (roomCenter ρ U M)]
      fun _ => -γ * (roomCenter ρ U M) 0 := by
    filter_upwards [Metric.ball_mem_nhds (roomCenter ρ U M)
      (by positivity : 0 < ρ / 4)] with x hx
    exact chainValue_terminal_core hρ U V hU x (le_of_lt hx)
  rw [heq.gradient_eq, gradient_const]

end NCBall
