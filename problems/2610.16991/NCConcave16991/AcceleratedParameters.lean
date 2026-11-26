import NCConcave16991.AcceleratedGap

/-! # Public accelerated horizon, residual tolerance, and genuine primal certificate -/

noncomputable section

open Set
open scoped InnerProductSpace BigOperators

namespace NCConcave16991.Accelerated

/-- The actual public horizon in equation (C.7), including its natural ceiling. -/
def horizon (τ DY δ : ℝ) : ℕ := max 1 (Nat.ceil (2 * Real.sqrt (τ * DY ^ 2 / δ)))

/-- The residual tolerance prescribed for that horizon and a positive diameter sum. -/
def tolerance (τ DY δ d : ℝ) : ℝ := δ / (2 * (horizon τ DY δ : ℝ) * d)

 theorem horizon_pos (τ DY δ : ℝ) : 0 < horizon τ DY δ :=
  lt_of_lt_of_le (by decide : 0 < 1) (Nat.le_max_left _ _)

 theorem horizon_lower (τ DY δ : ℝ) :
    2 * Real.sqrt (τ * DY ^ 2 / δ) ≤ (horizon τ DY δ : ℝ) := by
  have hm : (Nat.ceil (2 * Real.sqrt (τ * DY ^ 2 / δ)) : ℝ) ≤ (horizon τ DY δ : ℝ) := by
    exact Nat.cast_le.mpr (Nat.le_max_right 1 (Nat.ceil (2 * Real.sqrt (τ * DY ^ 2 / δ))))
  exact (Nat.le_ceil _).trans hm

 theorem tolerance_pos {τ DY δ d : ℝ} (hδ : 0 < δ) (hd : 0 < d) : 0 < tolerance τ DY δ d := by
  have hK : (0 : ℝ) < horizon τ DY δ := by exact_mod_cast horizon_pos τ DY δ
  dsimp [tolerance]
  positivity

 theorem horizon_quadratic_error {τ DY δ : ℝ} (hτ : 0 < τ) (hδ : 0 < δ) :
    2 * τ * DY ^ 2 / ((horizon τ DY δ : ℝ) + 1) ^ 2 ≤ δ / 2 := by
  let K := horizon τ DY δ
  let b := τ * DY ^ 2 / δ
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hs := Real.sq_sqrt hb
  have hK := horizon_lower τ DY δ
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hsq : 4 * b ≤ (K : ℝ) ^ 2 := by
    change 2 * Real.sqrt b ≤ (K : ℝ) at hK
    nlinarith [Real.sqrt_nonneg b]
  have hm := mul_le_mul_of_nonneg_left hsq hδ.le
  have hid : δ * b = τ * DY ^ 2 := by dsimp [b]; field_simp [hδ.ne'] <;> ring
  have hquad : 4 * τ * DY ^ 2 ≤ δ * (K : ℝ) ^ 2 := by nlinarith
  change 2 * τ * DY ^ 2 / ((K : ℝ) + 1) ^ 2 ≤ δ / 2
  apply (div_le_iff₀ (by positivity : 0 < ((K : ℝ) + 1) ^ 2)).mpr
  nlinarith [mul_nonneg hδ.le hK0]

 theorem tolerance_total {τ DY δ d : ℝ} (hd : 0 < d) :
    (horizon τ DY δ : ℝ) * d * tolerance τ DY δ d = δ / 2 := by
  have hK : (0 : ℝ) < horizon τ DY δ := by exact_mod_cast horizon_pos τ DY δ
  dsimp [tolerance]
  field_simp [hK.ne', hd.ne'] <;> ring

 theorem public_gap_error {τ DY δ d : ℝ} (hτ : 0 < τ) (hδ : 0 < δ) (hd : 0 < d) :
    2 * τ * DY ^ 2 / ((horizon τ DY δ : ℝ) + 1) ^ 2 +
      (horizon τ DY δ : ℝ) * d * tolerance τ DY δ d ≤ δ := by
  rw [tolerance_total hd]
  linarith [horizon_quadratic_error (DY := DY) hτ hδ]

variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- The genuine compact primal minimax value, with no chosen optimizer as a premise. -/
def primalOptimum (F : CompactSaddle X Y) : ℝ := sInf (primalValue F '' F.primal)

/-- The prescribed finite horizon and checked tolerance imply an actual primal-dual gap at most δ. -/
theorem source_primal_dual_gap (F : CompactSaddle X Y) {τ δ DX DY : ℝ}
    (hτ : 0 < τ) (hδ : 0 < δ) (hd : 0 < DX + DY)
    (hDX : ∀ x ∈ F.primal, ∀ u ∈ F.primal, ‖x - u‖ ≤ DX)
    (hDY : ∀ y ∈ F.dual, ∀ w ∈ F.dual, ‖y - w‖ ≤ DY)
    (solve : ℕ → Y → ProxResult (X := X) (Y := Y)) {y0 : Y} (hy0 : y0 ∈ F.dual)
    (hcheck : ∀ k < horizon τ DY δ,
      ResidualCheck F τ (tolerance τ DY δ (DX + DY))
        (center τ k (states τ solve y0 k)) (resultAt τ solve y0 k)) :
    primalValue F (primalOutput τ solve y0 (horizon τ DY δ)) +
      dualValue F (states τ solve y0 (horizon τ DY δ)).y ≤ δ := by
  exact (primal_dual_gap_quadratic F hτ (tolerance_pos hδ hd).le hDX hDY solve hy0
    (horizon_pos τ DY δ) hcheck).trans (public_gap_error hτ hδ hd)

/-- The output is an actual primal objective certificate against the genuine minimax value. -/
theorem source_primal_certificate (F : CompactSaddle X Y) {τ δ DX DY : ℝ}
    (hτ : 0 < τ) (hδ : 0 < δ) (hd : 0 < DX + DY)
    (hDX : ∀ x ∈ F.primal, ∀ u ∈ F.primal, ‖x - u‖ ≤ DX)
    (hDY : ∀ y ∈ F.dual, ∀ w ∈ F.dual, ‖y - w‖ ≤ DY)
    (solve : ℕ → Y → ProxResult (X := X) (Y := Y)) {y0 : Y} (hy0 : y0 ∈ F.dual)
    (hcheck : ∀ k < horizon τ DY δ,
      ResidualCheck F τ (tolerance τ DY δ (DX + DY))
        (center τ k (states τ solve y0 k)) (resultAt τ solve y0 k)) :
    primalValue F (primalOutput τ solve y0 (horizon τ DY δ)) ≤ primalOptimum F + δ := by
  have hgap := source_primal_dual_gap F hτ hδ hd hDX hDY solve hy0 hcheck
  have hy := dual_feasible F solve hy0 hcheck (le_rfl : horizon τ DY δ ≤ horizon τ DY δ)
  have hbound : primalValue F (primalOutput τ solve y0 (horizon τ DY δ)) - δ ≤ primalOptimum F := by
    apply le_csInf (F.primal_nonempty.image _)
    rintro q ⟨x, hx, rfl⟩
    have hn := negative_section_le_dual F hx hy
    have hp := section_le_primal F hx hy
    linarith
  linarith

/-- The paper's single Euclidean residual check, including explicit feasible normals. -/
def JointCheck (F : CompactSaddle X Y) (τ ζ : ℝ) (v : Y)
    (r : ProxResult (X := X) (Y := Y)) : Prop :=
  r.x ∈ F.primal ∧ r.y ∈ F.dual ∧ r.normalX ∈ SVRG.normalCone F.primal r.x ∧
    r.normalY ∈ SVRG.normalCone F.dual r.y ∧ ‖jointResidual F τ v r‖ ≤ ζ

 theorem JointCheck.toResidualCheck {F : CompactSaddle X Y} {τ ζ : ℝ} {v : Y}
    {r : ProxResult (X := X) (Y := Y)} (h : JointCheck F τ ζ v r) : ResidualCheck F τ ζ v r :=
  residualCheck_of_joint F h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

/-- The full public primal certificate follows directly from the actual joint residual checks. -/
theorem source_primal_certificate_of_joint_checks (F : CompactSaddle X Y) {τ δ DX DY : ℝ}
    (hτ : 0 < τ) (hδ : 0 < δ) (hd : 0 < DX + DY)
    (hDX : ∀ x ∈ F.primal, ∀ u ∈ F.primal, ‖x - u‖ ≤ DX)
    (hDY : ∀ y ∈ F.dual, ∀ w ∈ F.dual, ‖y - w‖ ≤ DY)
    (solve : ℕ → Y → ProxResult (X := X) (Y := Y)) {y0 : Y} (hy0 : y0 ∈ F.dual)
    (hcheck : ∀ k < horizon τ DY δ,
      JointCheck F τ (tolerance τ DY δ (DX + DY))
        (center τ k (states τ solve y0 k)) (resultAt τ solve y0 k)) :
    primalValue F (primalOutput τ solve y0 (horizon τ DY δ)) ≤ primalOptimum F + δ :=
  source_primal_certificate F hτ hδ hd hDX hDY solve hy0 (fun k hk ↦ (hcheck k hk).toResidualCheck)

end NCConcave16991.Accelerated


