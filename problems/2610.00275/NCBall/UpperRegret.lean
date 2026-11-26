import NCBall.UpperProjection

/-! # Deterministic regret of the clipped online update in the upper algorithm

These estimates hold on every realized sequence of gradient estimates. They
do not assume an unbiased oracle or the stochastic convergence theorem.
-/

noncomputable section
open Set Metric MeasureTheory
open scoped InnerProductSpace BigOperators
namespace NCBall

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def clippedIncrement (D : ℝ) (hD : 0 ≤ D) (α : ℝ) (g : ℕ → E) : ℕ → E
  | 0 => 0
  | t + 1 => ballProjection D hD (clippedIncrement D hD α g t - α • g t)

theorem clippedIncrement_norm_le (D : ℝ) (hD : 0 ≤ D) (α : ℝ) (g : ℕ → E) (t : ℕ) :
    ‖clippedIncrement D hD α g t‖ ≤ D := by
  cases t with
  | zero => simpa only [clippedIncrement, norm_zero] using hD
  | succ t => simpa only [clippedIncrement, mem_closedBall, dist_zero_right] using
      ballProjection_mem D hD (clippedIncrement D hD α g t - α • g t)

theorem clippedIncrement_measurable {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (D : ℝ) (hD : 0 ≤ D) (α : ℝ) (g : ℕ → Ω → E) (hg : ∀ t, Measurable (g t)) (t : ℕ) :
    Measurable (fun ω => clippedIncrement D hD α (fun s => g s ω) t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih => exact (ballProjection_measurable D hD).comp (ih.sub ((hg t).const_smul α))

theorem clipped_regret_step (D : ℝ) (hD : 0 ≤ D) (α : ℝ) (g : ℕ → E)
    (u : E) (hu : ‖u‖ ≤ D) (t : ℕ) :
    2 * α * ⟪g t, clippedIncrement D hD α g t - u⟫_ℝ ≤
      ‖clippedIncrement D hD α g t - u‖ ^ 2 -
        ‖clippedIncrement D hD α g (t + 1) - u‖ ^ 2 + α ^ 2 * ‖g t‖ ^ 2 := by
  let v := clippedIncrement D hD α g t
  have hp := ballProjection_distance_le D hD (v - α • g t) hu
  have he : (v - α • g t) - u = (v - u) - α • g t := by abel
  have hn := norm_sub_sq_real (v - u) (α • g t)
  rw [real_inner_smul_right, ← real_inner_comm (v - u) (g t), norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs] at hn
  rw [he] at hp
  change ‖clippedIncrement D hD α g (t + 1) - u‖ ≤ ‖(v - u) - α • g t‖ at hp
  have hsq := sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr hp
  change 2 * α * ⟪g t, v - u⟫_ℝ ≤ _
  nlinarith

theorem clipped_regret_energy (D : ℝ) (hD : 0 ≤ D) (α : ℝ) (g : ℕ → E)
    (u : E) (hu : ‖u‖ ≤ D) (s T : ℕ) :
    2 * α * (∑ t ∈ Finset.range T, ⟪g (s + t), clippedIncrement D hD α g (s + t) - u⟫_ℝ) ≤
      ‖clippedIncrement D hD α g s - u‖ ^ 2 - ‖clippedIncrement D hD α g (s + T) - u‖ ^ 2 +
        α ^ 2 * ∑ t ∈ Finset.range T, ‖g (s + t)‖ ^ 2 := by
  induction T with
  | zero => simp
  | succ T ih =>
    have hs := clipped_regret_step D hD α g u hu (s + T)
    simp only [Finset.sum_range_succ]
    rw [show s + (T + 1) = s + T + 1 by omega]
    nlinarith

theorem clipped_block_regret (D : ℝ) (hD : 0 ≤ D) {α : ℝ} (hα : 0 < α) (g : ℕ → E)
    (u : E) (hu : ‖u‖ ≤ D) (s T : ℕ) :
    (∑ t ∈ Finset.range T, ⟪g (s + t), clippedIncrement D hD α g (s + t) - u⟫_ℝ) ≤
      2 * D ^ 2 / α + (α / 2) * ∑ t ∈ Finset.range T, ‖g (s + t)‖ ^ 2 := by
  have he := clipped_regret_energy D hD α g u hu s T
  have hstart : ‖clippedIncrement D hD α g s - u‖ ≤ 2 * D := by
    have := norm_sub_le (clippedIncrement D hD α g s) u
    linarith [clippedIncrement_norm_le D hD α g s]
  have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 2 * D)).mpr hstart
  calc
    _ ≤ (4 * D ^ 2 + α ^ 2 * ∑ t ∈ Finset.range T, ‖g (s + t)‖ ^ 2) / (2 * α) := by
      apply (le_div_iff₀ (by positivity : 0 < 2 * α)).mpr
      nlinarith [sq_nonneg ‖clippedIncrement D hD α g (s + T) - u‖]
    _ = _ := by field_simp; ring

end NCBall
