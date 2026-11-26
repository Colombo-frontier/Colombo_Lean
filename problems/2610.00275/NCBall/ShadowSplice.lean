import NCBall.ShadowValue

/-! # Isolating one hidden direction in the concrete shadow response -/

noncomputable section
open scoped BigOperators InnerProductSpace
namespace NCBall

theorem roomCenter_update_of_le {n : ℕ} (ρ : ℝ) (U : ℕ → Space n)
    (j k : ℕ) (u : Space n) (hk : k ≤ j) :
    roomCenter ρ (Function.update U j u) k = roomCenter ρ U k := by
  unfold roomCenter
  congr 2
  apply Finset.sum_congr rfl
  intro i hi
  have hij : i ≠ j := by have := Finset.mem_range.mp hi; omega
  simp only [Function.update_of_ne hij]

theorem shadowValue_congr_prefix {n : ℕ} {M r : ℕ} (hr : r < M)
    (ρ γ lam : ℝ) (c c' V V' : ℕ → Space n) (x : Space n)
    (hc : ∀ k ≤ r, c k = c' k) (hV : ∀ k ≤ r, V k = V' k) :
    shadowValue M r ρ γ lam c V x = shadowValue M r ρ γ lam c' V' x := by
  rw [shadowValue_prefix hr, shadowValue_prefix hr]
  congr 2
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ r := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk
  rw [hc k hk', hV k hk']

theorem shadowPastValue_congr {n : ℕ} (r : ℕ) (ρ γ lam : ℝ)
    (c c' V V' : ℕ → Space n) (x : Space n)
    (hc : ∀ k < r, c k = c' k) (hV : ∀ k < r, V k = V' k) :
    shadowPastValue r ρ γ lam c V x = shadowPastValue r ρ γ lam c' V' x := by
  unfold shadowPastValue
  congr 2
  apply Finset.sum_congr rfl
  intro k hk
  rw [hc k (Finset.mem_range.mp hk), hV k (Finset.mem_range.mp hk)]

/-- Earlier shadow stages are completely independent of the spliced hidden
direction and its sample noise. -/
theorem shadow_before_spliced_room {n : ℕ} {M r j : ℕ} (hr : r < M) (hrj : r < j)
    (ρ γ lam : ℝ) (U V : ℕ → Space n) (u z x : Space n) :
    shadowValue M r ρ γ lam (roomCenter ρ (Function.update U j u)) (Function.update V j z) x =
      shadowValue M r ρ γ lam (roomCenter ρ U) V x := by
  apply shadowValue_congr_prefix hr
  · intro k hk
    exact roomCenter_update_of_le ρ U j k u (by omega)
  · intro k hk
    simp only [Function.update_of_ne (show k ≠ j by omega)]

/-- At the spliced room itself the unknown direction and sample noise enter
only through one affine scalar observation. -/
theorem shadow_at_spliced_room {n : ℕ} {M j : ℕ} (hj : j < M)
    (ρ γ lam σ : ℝ) (U V : ℕ → Space n) (u z x : Space n) :
    shadowValue M j ρ γ lam (roomCenter ρ (Function.update U j u))
      (Function.update V j (u + σ • z)) x =
      shadowPastValue j ρ γ lam (roomCenter ρ U) V x +
        ⟪u + σ • z, roomMeasurement ρ lam (roomCenter ρ U j) x⟫_ℝ := by
  rw [shadowValue_affine_current hj, Function.update_self,
    roomCenter_update_of_le ρ U j j u le_rfl]
  congr 1
  apply shadowPastValue_congr
  · intro k hk
    exact roomCenter_update_of_le ρ U j k u (by omega)
  · intro k hk
    simp only [Function.update_of_ne (show k ≠ j by omega)]

end NCBall
