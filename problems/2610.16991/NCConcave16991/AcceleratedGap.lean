import NCConcave16991.AcceleratedSteps

/-! # Accelerated primal-dual gap for the actual primal output -/

noncomputable section

open Set
open scoped InnerProductSpace BigOperators

namespace NCConcave16991.Accelerated

variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

 theorem mass_pos {τ : ℝ} (hτ : 0 < τ) {K : ℕ} (hK : 0 < K) : 0 < mass τ K := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hK)
  exact mass_succ_pos hτ k

 theorem dual_feasible (F : CompactSaddle X Y) {τ ζ : ℝ}
    (solve : ℕ → Y → ProxResult (X := X) (Y := Y)) {y0 : Y} (hy0 : y0 ∈ F.dual) {K : ℕ}
    (hcheck : ∀ k < K, ResidualCheck F τ ζ (center τ k (states τ solve y0 k)) (resultAt τ solve y0 k))
    {k : ℕ} (hk : k ≤ K) : (states τ solve y0 k).y ∈ F.dual := by
  cases k with
  | zero => exact hy0
  | succ k => exact (hcheck k (by omega)).2.1

 theorem primalOutput_eq_centerMass (τ : ℝ) (solve : ℕ → Y → ProxResult (X := X) (Y := Y))
    (y0 : Y) (K : ℕ) :
    primalOutput τ solve y0 K = (Finset.range K).centerMass (weight τ) (fun k ↦ (resultAt τ solve y0 k).x) := by
  simp only [primalOutput, primalSum_eq, Finset.centerMass, sum_weights]

 theorem primalOutput_mem (F : CompactSaddle X Y) {τ ζ : ℝ} (hτ : 0 < τ)
    (solve : ℕ → Y → ProxResult (X := X) (Y := Y)) (y0 : Y) {K : ℕ} (hK : 0 < K)
    (hcheck : ∀ k < K, ResidualCheck F τ ζ (center τ k (states τ solve y0 k)) (resultAt τ solve y0 k)) :
    primalOutput τ solve y0 K ∈ F.primal := by
  rw [primalOutput_eq_centerMass]
  apply F.primal_convex.centerMass_mem
  · intro k hk
    exact (weight_pos hτ k).le
  · rw [sum_weights]
    exact mass_pos hτ hK
  · intro k hk
    exact (hcheck k (Finset.mem_range.mp hk)).1

 theorem primalOutput_jensen (F : CompactSaddle X Y) {τ ζ : ℝ} (hτ : 0 < τ)
    (solve : ℕ → Y → ProxResult (X := X) (Y := Y)) (y0 : Y) {K : ℕ} (hK : 0 < K)
    (hcheck : ∀ k < K, ResidualCheck F τ ζ (center τ k (states τ solve y0 k)) (resultAt τ solve y0 k))
    {target : Y} (htarget : target ∈ F.dual) :
    mass τ K * F.objective (primalOutput τ solve y0 K) target ≤
      ∑ k ∈ Finset.range K, weight τ k * F.objective (resultAt τ solve y0 k).x target := by
  have hm := mass_pos hτ hK
  have hj := (F.convexX target htarget).map_centerMass_le
    (t := Finset.range K) (w := weight τ) (p := fun k ↦ (resultAt τ solve y0 k).x)
    (fun k _ ↦ (weight_pos hτ k).le) (by rw [sum_weights]; exact hm)
    (fun k hk ↦ (hcheck k (Finset.mem_range.mp hk)).1)
  have hj' : F.objective (primalOutput τ solve y0 K) target ≤
      (mass τ K)⁻¹ * ∑ k ∈ Finset.range K, weight τ k * F.objective (resultAt τ solve y0 k).x target := by
    simpa only [Finset.centerMass, sum_weights, Function.comp_apply, ← primalSum_eq,
      primalOutput, smul_eq_mul] using hj
  have h := mul_le_mul_of_nonneg_left hj' hm.le
  simpa only [← mul_assoc, mul_inv_cancel₀ hm.ne', one_mul] using h

/-- Summing the actually proved potential step yields the exact estimate sequence. -/
theorem potential_telescope (F : CompactSaddle X Y) {τ ζ DX DY : ℝ} (hτ : 0 < τ)
    (hDX : ∀ x ∈ F.primal, ∀ u ∈ F.primal, ‖x - u‖ ≤ DX)
    (hDY : ∀ y ∈ F.dual, ∀ w ∈ F.dual, ‖y - w‖ ≤ DY)
    (solve : ℕ → Y → ProxResult (X := X) (Y := Y)) {y0 : Y} (hy0 : y0 ∈ F.dual) (K : ℕ)
    (hcheck : ∀ k < K, ResidualCheck F τ ζ (center τ k (states τ solve y0 k)) (resultAt τ solve y0 k))
    {target : Y} (htarget : target ∈ F.dual) :
    mass τ K * dualValue F (states τ solve y0 K).y + ‖(states τ solve y0 K).z - target‖ ^ 2 / 2 +
      (∑ k ∈ Finset.range K, weight τ k * F.objective (resultAt τ solve y0 k).x target) ≤
      ‖y0 - target‖ ^ 2 / 2 + ((DX + DY) * ζ) * ∑ k ∈ Finset.range K, mass τ (k + 1) := by
  have hsum : ∀ j, j ≤ K →
      mass τ j * dualValue F (states τ solve y0 j).y + ‖(states τ solve y0 j).z - target‖ ^ 2 / 2 +
        (∑ k ∈ Finset.range j, weight τ k * F.objective (resultAt τ solve y0 k).x target) ≤
      ‖y0 - target‖ ^ 2 / 2 + ((DX + DY) * ζ) * ∑ k ∈ Finset.range j, mass τ (k + 1) := by
    intro j
    induction j with
    | zero => intro _; simp [mass, states]
    | succ j ih =>
      intro hj
      have hp := checked_potential_step F hτ hDX hDY solve y0 j (hcheck j (by omega))
        (dual_feasible F solve hy0 hcheck (by omega : j ≤ K)) htarget
      have hi := ih (by omega)
      simp only [Finset.sum_range_succ]
      nlinarith
  exact hsum K le_rfl

 theorem sum_masses_le {τ : ℝ} (hτ : 0 < τ) (K : ℕ) :
    (∑ k ∈ Finset.range K, mass τ (k + 1)) ≤ (K : ℝ) * mass τ K := by
  calc
    _ ≤ ∑ _k ∈ Finset.range K, mass τ K := by
      apply Finset.sum_le_sum
      intro k hk
      exact mass_monotone hτ (Nat.succ_le_of_lt (Finset.mem_range.mp hk))
    _ = _ := by simp

/-- The source gap bound is a bound on the actual max-minus-min saddle gap. -/
theorem primal_dual_gap (F : CompactSaddle X Y) {τ ζ DX DY : ℝ} (hτ : 0 < τ) (hζ : 0 ≤ ζ)
    (hDX : ∀ x ∈ F.primal, ∀ u ∈ F.primal, ‖x - u‖ ≤ DX)
    (hDY : ∀ y ∈ F.dual, ∀ w ∈ F.dual, ‖y - w‖ ≤ DY)
    (solve : ℕ → Y → ProxResult (X := X) (Y := Y)) {y0 : Y} (hy0 : y0 ∈ F.dual) {K : ℕ} (hK : 0 < K)
    (hcheck : ∀ k < K, ResidualCheck F τ ζ (center τ k (states τ solve y0 k)) (resultAt τ solve y0 k)) :
    primalValue F (primalOutput τ solve y0 K) + dualValue F (states τ solve y0 K).y ≤
      DY ^ 2 / (2 * mass τ K) + (K : ℝ) * (DX + DY) * ζ := by
  have hm := mass_pos hτ hK
  have hDX0 : 0 ≤ DX := by obtain ⟨x, hx⟩ := F.primal_nonempty; simpa using hDX x hx x hx
  have hDY0 : 0 ≤ DY := by simpa using hDY y0 hy0 y0 hy0
  have he : 0 ≤ (DX + DY) * ζ := mul_nonneg (add_nonneg hDX0 hDY0) hζ
  have hpoint (target : Y) (htarget : target ∈ F.dual) :
      F.objective (primalOutput τ solve y0 K) target + dualValue F (states τ solve y0 K).y ≤
        DY ^ 2 / (2 * mass τ K) + (K : ℝ) * (DX + DY) * ζ := by
    have ht := potential_telescope F hτ hDX hDY solve hy0 K hcheck htarget
    have hj := primalOutput_jensen F hτ solve y0 hK hcheck htarget
    have hz := sq_nonneg ‖(states τ solve y0 K).z - target‖
    have hd := pow_le_pow_left₀ (norm_nonneg _) (hDY y0 hy0 target htarget) 2
    have hs := mul_le_mul_of_nonneg_left (sum_masses_le hτ K) he
    have hb : mass τ K * (F.objective (primalOutput τ solve y0 K) target + dualValue F (states τ solve y0 K).y) ≤
        DY ^ 2 / 2 + (K : ℝ) * mass τ K * ((DX + DY) * ζ) := by nlinarith
    have hq : F.objective (primalOutput τ solve y0 K) target + dualValue F (states τ solve y0 K).y ≤
        (DY ^ 2 / 2 + (K : ℝ) * mass τ K * ((DX + DY) * ζ)) / mass τ K :=
      (le_div_iff₀ hm).mpr (by nlinarith [hb])
    have hid : (DY ^ 2 / 2 + (K : ℝ) * mass τ K * ((DX + DY) * ζ)) / mass τ K =
        DY ^ 2 / (2 * mass τ K) + (K : ℝ) * (DX + DY) * ζ := by field_simp [hm.ne'] <;> ring
    rw [hid] at hq
    exact hq
  have hs : primalValue F (primalOutput τ solve y0 K) ≤
      DY ^ 2 / (2 * mass τ K) + (K : ℝ) * (DX + DY) * ζ - dualValue F (states τ solve y0 K).y := by
    apply csSup_le (F.dual_nonempty.image _)
    rintro v ⟨target, ht, rfl⟩
    linarith [hpoint target ht]
  linarith

 theorem primal_dual_gap_quadratic (F : CompactSaddle X Y) {τ ζ DX DY : ℝ} (hτ : 0 < τ) (hζ : 0 ≤ ζ)
    (hDX : ∀ x ∈ F.primal, ∀ u ∈ F.primal, ‖x - u‖ ≤ DX)
    (hDY : ∀ y ∈ F.dual, ∀ w ∈ F.dual, ‖y - w‖ ≤ DY)
    (solve : ℕ → Y → ProxResult (X := X) (Y := Y)) {y0 : Y} (hy0 : y0 ∈ F.dual) {K : ℕ} (hK : 0 < K)
    (hcheck : ∀ k < K, ResidualCheck F τ ζ (center τ k (states τ solve y0 k)) (resultAt τ solve y0 k)) :
    primalValue F (primalOutput τ solve y0 K) + dualValue F (states τ solve y0 K).y ≤
      2 * τ * DY ^ 2 / ((K : ℝ) + 1) ^ 2 + (K : ℝ) * (DX + DY) * ζ := by
  have h := primal_dual_gap F hτ hζ hDX hDY solve hy0 hK hcheck
  have hi := mul_le_mul_of_nonneg_right (inverse_mass_bound hτ hK) (sq_nonneg DY)
  have hi' : DY ^ 2 / (2 * mass τ K) ≤ 2 * τ * DY ^ 2 / ((K : ℝ) + 1) ^ 2 := by convert hi using 1 <;> ring
  linarith

end NCConcave16991.Accelerated

