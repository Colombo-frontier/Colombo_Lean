import NCBall.ChainAnalytic

/-! # Value bounds and the initial gap on the query ball -/

noncomputable section
open Set Metric
open scoped BigOperators InnerProductSpace
namespace NCBall

theorem radialLinearBump_value_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (v x : E) : ‖radialLinearBump v x‖ ≤ ‖v‖ := by
  by_cases hx : ‖x‖ ≤ 1
  · have hc := radialCutoff_range x
    have hi : ‖⟪v, x⟫_ℝ‖ ≤ ‖v‖ :=
      (norm_inner_le_norm v x).trans (by nlinarith [norm_nonneg v])
    rw [radialLinearBump, norm_mul, Real.norm_eq_abs, abs_of_nonneg hc.1]
    exact (mul_le_mul_of_nonneg_left hi hc.1).trans (by nlinarith [norm_nonneg v])
  · simp [radialLinearBump, radialCutoff_zero (le_of_lt (lt_of_not_ge hx))]

theorem scaledBump_value_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {a ρ : ℝ} (ha : 0 ≤ a) (hρ : 0 ≤ ρ) (c v x : E) :
    ‖scaledBump a ρ c v x‖ ≤ a * ρ * ‖v‖ := by
  rw [scaledBump, norm_mul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ha hρ)]
  exact mul_le_mul_of_nonneg_left (radialLinearBump_value_bound v _) (mul_nonneg ha hρ)

theorem room_value_sum_bound {n M : ℕ} {ρ lam B : ℝ}
    (hρ : 0 < ρ) (hlam : 0 ≤ lam) (hB : 0 ≤ B)
    (U V : ℕ → Space n) (hU : ∀ i, U i 0 = 0)
    (hV : ∀ i < M, ‖V i‖ ≤ B) (x : Space n) :
    ‖∑ j ∈ Finset.range M, scaledBump lam ρ (roomCenter ρ U j) (V j) x‖ ≤
      lam * ρ * B := by
  apply norm_sum_disjoint_support (Finset.range M)
    (fun j => closedBall (roomCenter ρ U j) ρ) _ x (by positivity)
  · intro i hi j hj hij
    exact rooms_disjoint hρ U hU hij
  · intro i hi hx
    exact scaledBump_zero_off lam hρ _ _ x hx
  · intro i hi
    exact (scaledBump_value_bound hlam hρ.le _ _ x).trans
      (mul_le_mul_of_nonneg_left (hV i (Finset.mem_range.mp hi)) (by positivity))

theorem chainValue_deviation_bound {n M : ℕ} {ρ γ lam B : ℝ}
    (hρ : 0 < ρ) (hγ : 0 ≤ γ) (hlam : 0 ≤ lam) (hB : 0 ≤ B)
    (U V : ℕ → Space n) (hU : ∀ i, U i 0 = 0)
    (hV : ∀ i < M, ‖V i‖ ≤ B) (x : Space n) :
    |chainValue M ρ γ lam (roomCenter ρ U) V x + γ * x 0| ≤ lam * ρ * B + γ * ρ := by
  have hs := room_value_sum_bound hρ hlam hB U V hU hV x
  have ht := scaledBump_value_bound hγ hρ.le (roomCenter ρ U M)
    (EuclideanSpace.single 0 1) x
  simp only [EuclideanSpace.norm_single, norm_one, mul_one] at ht
  rw [chainValue_decompose]
  have heq : -γ * x 0 +
      ∑ j ∈ Finset.range M, scaledBump lam ρ (roomCenter ρ U j) (V j) x +
      scaledBump γ ρ (roomCenter ρ U M) (EuclideanSpace.single 0 1) x + γ * x 0 =
      (∑ j ∈ Finset.range M, scaledBump lam ρ (roomCenter ρ U j) (V j) x) +
      scaledBump γ ρ (roomCenter ρ U M) (EuclideanSpace.single 0 1) x := by ring
  rw [heq, ← Real.norm_eq_abs]
  exact (norm_add_le _ _).trans (add_le_add hs ht)

theorem chainValue_at_origin {n M : ℕ} {ρ γ lam : ℝ}
    (hρ : 0 < ρ) (hM : 1 ≤ M) (U V : ℕ → Space n) (hU : ∀ i, U i 0 = 0) :
    chainValue M ρ γ lam (roomCenter ρ U) V 0 = 0 := by
  have hzero : (0 : Space n) ∈ closedBall (roomCenter ρ U 0) ρ := by
    simp [roomCenter_zero, hρ.le]
  have hout (j : ℕ) (hj : j ≠ 0) : (0 : Space n) ∉ closedBall (roomCenter ρ U j) ρ := by
    intro hx
    exact Set.disjoint_left.mp (rooms_disjoint hρ U hU hj) hx hzero
  have hs : ∑ j ∈ Finset.range M, scaledBump lam ρ (roomCenter ρ U j) (V j) 0 = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    by_cases hj0 : j = 0
    · subst j
      simp [scaledBump, roomCenter_zero, radialLinearBump]
    · exact scaledBump_zero_off lam hρ _ _ 0 (hout j hj0)
  rw [chainValue_decompose, hs, scaledBump_zero_off γ hρ _ _ 0 (hout M (by omega))]
  simp

theorem chainValue_gap_pointwise {n M : ℕ} {ρ γ lam B R : ℝ}
    (hρ : 0 < ρ) (hM : 1 ≤ M) (hγ : 0 ≤ γ) (hlam : 0 ≤ lam) (hB : 0 ≤ B)
    (U V : ℕ → Space n) (hU : ∀ i, U i 0 = 0)
    (hV : ∀ i < M, ‖V i‖ ≤ B) (x : Space n) (hx : x ∈ closedBall 0 R) :
    chainValue M ρ γ lam (roomCenter ρ U) V 0 -
      chainValue M ρ γ lam (roomCenter ρ U) V x ≤ γ * R + lam * ρ * B + γ * ρ := by
  rw [chainValue_at_origin hρ hM U V hU]
  have hd := (abs_le.mp (chainValue_deviation_bound hρ hγ hlam hB U V hU hV x)).1
  have hcoord : x 0 ≤ R := by
    have hc := clock_dist_le x 0
    simp only [PiLp.zero_apply, sub_zero, dist_zero_right] at hc
    have hn : ‖x‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hx
    exact (le_abs_self _).trans (hc.trans hn)
  nlinarith [mul_le_mul_of_nonneg_left hcoord hγ]

/-- This uses the actual infimum on the ball, rather than assuming a gap. -/
theorem chainValue_gap_infimum {n M : ℕ} {ρ γ lam B R : ℝ}
    (hρ : 0 < ρ) (hM : 1 ≤ M) (hγ : 0 ≤ γ) (hlam : 0 ≤ lam) (hB : 0 ≤ B)
    (hR : 0 ≤ R) (U V : ℕ → Space n) (hU : ∀ i, U i 0 = 0)
    (hV : ∀ i < M, ‖V i‖ ≤ B) :
    chainValue M ρ γ lam (roomCenter ρ U) V 0 -
      sInf (chainValue M ρ γ lam (roomCenter ρ U) V '' closedBall 0 R) ≤
        γ * R + lam * ρ * B + γ * ρ := by
  have hne : (chainValue M ρ γ lam (roomCenter ρ U) V '' closedBall 0 R).Nonempty :=
    ⟨_, ⟨0, by simpa using hR, rfl⟩⟩
  have hb : chainValue M ρ γ lam (roomCenter ρ U) V 0 -
      (γ * R + lam * ρ * B + γ * ρ) ≤
      sInf (chainValue M ρ γ lam (roomCenter ρ U) V '' closedBall 0 R) := by
    apply le_csInf hne
    rintro y ⟨x, hx, rfl⟩
    have h := chainValue_gap_pointwise hρ hM hγ hlam hB U V hU hV x hx
    linarith
  linarith

end NCBall
