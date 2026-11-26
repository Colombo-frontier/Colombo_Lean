import NCConcave16991.AcceleratedLocalization

/-! # The public primal radius and an actual unrestricted inexact proximal certificate -/

noncomputable section

open Set Metric
open scoped InnerProductSpace

namespace NCConcave16991.Accelerated

/-- The public radius of Appendix C, for a known upper bound on the current objective gap. -/
def publicRadius (p : ProblemParameters) (Δ : ℝ) : ℝ :=
  3 * Real.sqrt (Δ / p.L) + 2 * p.diameter + p.epsilon / p.L

 theorem publicRadius_pos (p : ProblemParameters) (Δ : ℝ) : 0 < publicRadius p Δ := by
  have hL := p.L_pos
  have hD := p.diameter_nonneg
  have hε := p.epsilon_pos
  dsimp [publicRadius]
  positivity

 theorem mul_sqrt_div {L Δ : ℝ} (hL : 0 < L) (hΔ : 0 ≤ Δ) :
    L * Real.sqrt (Δ / L) = Real.sqrt (L * Δ) := by
  have h1 : (L * Real.sqrt (Δ / L)) ^ 2 = L * Δ := by
    rw [mul_pow, Real.sq_sqrt (div_nonneg hΔ hL.le)]
    field_simp [hL.ne'] <;> ring
  have h2 := Real.sq_sqrt (mul_nonneg hL.le hΔ)
  have hn1 := mul_nonneg hL.le (Real.sqrt_nonneg (Δ / L))
  have hn2 := Real.sqrt_nonneg (L * Δ)
  nlinarith

/-- The exact public radius strictly exceeds the center-gradient threshold. -/
theorem publicRadius_gradient_margin (p : ProblemParameters) {Δ : ℝ} (hΔ : 0 ≤ Δ) :
    3 * Real.sqrt (p.L * Δ) + p.L * p.diameter < p.L * publicRadius p Δ := by
  have hs := mul_sqrt_div p.L_pos hΔ
  have he : p.L * (p.epsilon / p.L) = p.epsilon := by field_simp [p.L_pos.ne']
  have hD := mul_nonneg p.L_pos.le p.diameter_nonneg
  have hε := p.epsilon_pos
  dsimp [publicRadius]
  nlinarith

variable {p : ProblemParameters} {dx dy : ℕ} {K : KnownDualDomain dy p.diameter}

/-- The actual compact region used by the accelerated proximal solver. -/
def ballSaddle (P : Problem p dx dy K) (hAS : P.averagedSmooth) (Δ : ℝ)
    (y0 : DualSpace dy) (c : PrimalSpace dx) : CompactSaddle (PrimalSpace dx) (DualSpace dy) :=
  compactProximalSaddle P hAS (closedBall c (publicRadius p Δ))
    ⟨c, by simpa using (publicRadius_pos p Δ).le⟩
    (isCompact_closedBall c (publicRadius p Δ)) (convex_closedBall c (publicRadius p Δ)) y0 c

 theorem closedBall_diameter (c : PrimalSpace dx) {R : ℝ}
    (x : PrimalSpace dx) (hx : x ∈ closedBall c R) (u : PrimalSpace dx) (hu : u ∈ closedBall c R) :
    ‖x - u‖ ≤ 2 * R := by
  have ht := dist_triangle x c u
  have hx' : ‖x - c‖ ≤ R := hx
  have hu' : ‖u - c‖ ≤ R := hu
  rw [dist_comm c u] at ht
  simp only [dist_eq_norm] at ht
  linarith

/-- The actual unrestricted proximal minimizer is in the exact public primal ball. -/
theorem publicRadius_contains_proximalMap (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    {Δ : ℝ} (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) (c : PrimalSpace dx)
    (hgap : primalObjective K P.component c - sInf (range (primalObjective K P.component)) ≤ Δ) :
    proximalMap p.L_pos (P.primal_continuous hAS) P.value_bddBelow c ∈ closedBall c (publicRadius p Δ) := by
  have hm := csInf_le P.value_bddBelow (mem_range_self c)
  have hΔ : 0 ≤ Δ := by linarith
  exact actual_proximalMap_mem_ball P hAS y0 hy0 c hgap (publicRadius_pos p Δ)
    (publicRadius_gradient_margin p hΔ)

/-- Successful checked accelerated solves on the public ball give an actual inexact
proximal point for the unrestricted original value function, with no localization premise. -/
theorem public_inexact_proximal_certificate (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    {Δ τ δ : ℝ} (hτ : 0 < τ) (hδ : 0 < δ)
    (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) (c : PrimalSpace dx)
    (hgap : primalObjective K P.component c - sInf (range (primalObjective K P.component)) ≤ Δ)
    (solve : ℕ → DualSpace dy → ProxResult (X := PrimalSpace dx) (Y := DualSpace dy))
    (hcheck : ∀ k < horizon τ p.diameter δ,
      JointCheck (ballSaddle P hAS Δ y0 c) τ
        (tolerance τ p.diameter δ (2 * publicRadius p Δ + p.diameter))
        (center τ k (states τ solve y0 k)) (resultAt τ solve y0 k)) :
    primalObjective K P.component (primalOutput τ solve y0 (horizon τ p.diameter δ)) +
      p.L * ‖primalOutput τ solve y0 (horizon τ p.diameter δ) - c‖ ^ 2 ≤
      primalObjective K P.component (proximalMap p.L_pos (P.primal_continuous hAS) P.value_bddBelow c) +
        p.L * ‖proximalMap p.L_pos (P.primal_continuous hAS) P.value_bddBelow c - c‖ ^ 2 + δ := by
  have hR := publicRadius_pos p Δ
  have hD := p.diameter_nonneg
  have hp := publicRadius_contains_proximalMap P hAS y0 hy0 c hgap
  exact actual_proximal_primal_certificate P hAS (closedBall c (publicRadius p Δ))
    ⟨c, by simpa using hR.le⟩ (isCompact_closedBall c (publicRadius p Δ))
    (convex_closedBall c (publicRadius p Δ)) y0 hy0 c hτ hδ (by positivity)
    (closedBall_diameter c) solve hcheck hp

end NCConcave16991.Accelerated
