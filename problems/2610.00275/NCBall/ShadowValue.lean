import NCBall.Construction
import NCBall.Coupling

/-! # The concrete shadow oracle suppressing unresolved future bumps -/

noncomputable section
open Set Metric
open scoped BigOperators InnerProductSpace ContDiff
namespace NCBall

def shadowValue {n : ℕ} (M r : ℕ) (ρ γ lam : ℝ)
    (c V : ℕ → Space n) (x : Space n) : ℝ :=
  -γ * x 0 + lam * ρ * ∑ j ∈ Finset.range M,
    (if j ≤ r then localBump (V j) (ρ⁻¹ • (x - c j)) else 0) +
    if M ≤ r then γ * ρ * terminalBump (ρ⁻¹ • (x - c M)) else 0

def earlyRoomHit {n : ℕ} (M r : ℕ) (ρ : ℝ)
    (c : ℕ → Space n) (x : Space n) : Prop :=
  ∃ j, r < j ∧ j ≤ M ∧ x ∈ closedBall (c j) ρ

theorem shadowValue_eq_real_of_no_early_hit {n : ℕ} (M r : ℕ)
    {ρ γ lam : ℝ} (hρ : 0 < ρ) (c V : ℕ → Space n) (x : Space n)
    (hsafe : ¬earlyRoomHit M r ρ c x) :
    shadowValue M r ρ γ lam c V x = chainValue M ρ γ lam c V x := by
  have hout (j : ℕ) (hj : r < j) (hM : j ≤ M) : ρ ≤ dist x (c j) := by
    have hn : x ∉ closedBall (c j) ρ := fun hx => hsafe ⟨j, hj, hM, hx⟩
    exact le_of_lt (by simpa only [mem_closedBall, not_le] using hn)
  have hs : (∑ j ∈ Finset.range M,
      if j ≤ r then localBump (V j) (ρ⁻¹ • (x - c j)) else 0) =
      ∑ j ∈ Finset.range M, localBump (V j) (ρ⁻¹ • (x - c j)) := by
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs with hr
    · rfl
    · exact (localBump_eq_zero_outside hρ x (c j) (V j)
        (hout j (Nat.lt_of_not_ge hr) (Nat.le_of_lt (Finset.mem_range.mp hj)))).symm
  unfold shadowValue chainValue
  rw [hs]
  by_cases hM : M ≤ r
  · rw [if_pos hM]
  · rw [if_neg hM, terminalBump_eq_zero_outside hρ x (c M)
      (hout M (Nat.lt_of_not_ge hM) le_rfl), mul_zero]

theorem shadowValue_all_unlocked {n : ℕ} (M r : ℕ) (hr : M ≤ r)
    (ρ γ lam : ℝ) (c V : ℕ → Space n) (x : Space n) :
    shadowValue M r ρ γ lam c V x = chainValue M ρ γ lam c V x := by
  have hs : ∀ j ∈ Finset.range M, j ≤ r := fun j hj =>
    (Nat.le_of_lt (Finset.mem_range.mp hj)).trans hr
  simp only [shadowValue, chainValue, if_pos hr]
  congr 3
  apply Finset.sum_congr rfl
  intro j hj
  rw [if_pos (hs j hj)]

theorem shadowValue_prefix {n : ℕ} {M r : ℕ} (hr : r < M)
    (ρ γ lam : ℝ) (c V : ℕ → Space n) (x : Space n) :
    shadowValue M r ρ γ lam c V x = -γ * x 0 +
      lam * ρ * ∑ j ∈ Finset.range (r + 1), localBump (V j) (ρ⁻¹ • (x - c j)) := by
  let f := fun j => if j ≤ r then localBump (V j) (ρ⁻¹ • (x - c j)) else 0
  have hs : (∑ j ∈ Finset.range (r + 1), f j) = ∑ j ∈ Finset.range M, f j := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro j _ hj
    simp only [Finset.mem_range, not_lt] at hj
    simp [f, show ¬j ≤ r by omega]
  rw [shadowValue, if_neg (Nat.not_le_of_lt hr), add_zero, ← hs]
  congr 2
  apply Finset.sum_congr rfl
  intro j hj
  exact if_pos (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj)

def shadowPastValue {n : ℕ} (r : ℕ) (ρ γ lam : ℝ)
    (c V : ℕ → Space n) (x : Space n) : ℝ :=
  -γ * x 0 + lam * ρ * ∑ j ∈ Finset.range r, localBump (V j) (ρ⁻¹ • (x - c j))

def roomMeasurement {n : ℕ} (ρ lam : ℝ) (c x : Space n) : Space n :=
  (lam * ρ * cutoff n (ρ⁻¹ • (x - c))) • (ρ⁻¹ • (x - c))

/-- The current room contributes one scalar; every other retained term uses
only past-room data. No membership test involving a future center occurs. -/
theorem shadowValue_affine_current {n : ℕ} {M r : ℕ} (hr : r < M)
    (ρ γ lam : ℝ) (c V : ℕ → Space n) (x : Space n) :
    shadowValue M r ρ γ lam c V x = shadowPastValue r ρ γ lam c V x +
      ⟪V r, roomMeasurement ρ lam (c r) x⟫_ℝ := by
  rw [shadowValue_prefix hr, Finset.sum_range_succ]
  simp only [shadowPastValue, roomMeasurement, localBump, real_inner_smul_right]
  ring

theorem roomMeasurement_zero_of_clock_miss {n : ℕ} {ρ lam : ℝ} (hρ : 0 < ρ)
    (c x : Space n) (hc : ρ < |x 0 - c 0|) : roomMeasurement ρ lam c x = 0 := by
  have hd : ρ ≤ dist x c := (le_of_lt hc).trans (clock_dist_le x c)
  have hn : 1 ≤ ‖ρ⁻¹ • (x - c)‖ := by
    rw [scaled_norm hρ]
    exact (le_div_iff₀ hρ).mpr (by simpa using hd)
  simp [roomMeasurement, cutoff_zero hn]

theorem shadowValue_smooth {n : ℕ} (M r : ℕ) (ρ γ lam : ℝ)
    (c V : ℕ → Space n) : ContDiff ℝ ∞ (shadowValue M r ρ γ lam c V) := by
  have hm (j : ℕ) : ContDiff ℝ ∞ (fun x => localBump (V j) (ρ⁻¹ • (x - c j))) :=
    (localBump_smooth (V j)).comp (contDiff_const.smul (contDiff_id.sub contDiff_const))
  unfold shadowValue
  apply ContDiff.add
  · apply ContDiff.add
    · exact contDiff_const.mul (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin (n + 1)) 0).contDiff
    · apply contDiff_const.mul
      apply ContDiff.sum
      intro j _
      by_cases hj : j ≤ r
      · simpa [hj] using hm j
      · simp only [hj, if_false]
        exact contDiff_const
  · by_cases hr : M ≤ r
    · simp only [hr, if_true]
      exact contDiff_const.mul ((terminalBump_smooth n).comp
        (contDiff_const.smul (contDiff_id.sub contDiff_const)))
    · simp only [hr, if_false]
      exact contDiff_const

end NCBall
