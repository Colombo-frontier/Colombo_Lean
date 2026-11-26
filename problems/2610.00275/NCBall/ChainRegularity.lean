import NCBall.ChainAnalytic

/-! # Global smoothness and the location of stationary points -/

noncomputable section
open Set Metric InnerProductSpace
open scoped BigOperators NNReal ContDiff
namespace NCBall

theorem room_gradient_sum_lipschitz {n M : ℕ} {ρ lam B : ℝ}
    (hρ : 0 < ρ) (hlam : 0 ≤ lam) (hB : 0 ≤ B)
    (U V : ℕ → Space n) (hU : ∀ i, U i 0 = 0)
    (hV : ∀ i < M, ‖V i‖ ≤ B) :
    LipschitzWith ⟨lam / ρ * bumpConstant * B, by
      have := bumpConstant_pos
      positivity⟩
      (fun x => ∑ j ∈ Finset.range M,
        scaledBumpGradient lam ρ (roomCenter ρ U j) (V j) x) := by
  apply sum_disjoint_lipschitz (Finset.range M)
    (fun j => closedBall (roomCenter ρ U j) ρ)
  · intro i hi
    exact isClosed_closedBall
  · intro i hi j hj hij
    exact rooms_disjoint hρ U hU hij
  · intro i hi x hx
    exact scaledBumpGradient_zero_off lam hρ _ _ x hx
  · intro i hi
    exact (scaledBumpGradient_smooth _ _ _ _).differentiable (by simp)
  · intro i hi x
    have hb := scaledBumpGradient_fderiv_bound hlam hρ (roomCenter ρ U i) (V i) x
    calc
      _ ≤ lam / ρ * (bumpConstant * ‖V i‖) := hb
      _ ≤ lam / ρ * (bumpConstant * B) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hV i (Finset.mem_range.mp hi)) bumpConstant_pos.le)
          (div_nonneg hlam hρ.le)
      _ = _ := by simp only [NNReal.coe_mk]; ring

theorem chainValue_gradient_norm_sub {n M : ℕ} {ρ γ lam B : ℝ}
    (hρ : 0 < ρ) (hγ : 0 ≤ γ) (hlam : 0 ≤ lam) (hB : 0 ≤ B)
    (U V : ℕ → Space n) (hU : ∀ i, U i 0 = 0)
    (hV : ∀ i < M, ‖V i‖ ≤ B) (x y : Space n) :
    ‖gradient (chainValue M ρ γ lam (roomCenter ρ U) V) x -
      gradient (chainValue M ρ γ lam (roomCenter ρ U) V) y‖ ≤
      ((lam * B + γ) * bumpConstant / ρ) * ‖x - y‖ := by
  have hs := (room_gradient_sum_lipschitz hρ hlam hB U V hU hV).dist_le_mul x y
  simp only [dist_eq_norm, NNReal.coe_mk] at hs
  have ht := scaledBumpGradient_norm_sub hγ hρ (roomCenter ρ U M)
    (EuclideanSpace.single 0 1) x y
  simp only [EuclideanSpace.norm_single, norm_one, mul_one] at ht
  rw [chainValue_gradient M hρ γ lam, chainValue_gradient M hρ γ lam]
  unfold chainGradient
  have heq :
      (-γ • EuclideanSpace.single 0 1 +
        ∑ j ∈ Finset.range M, scaledBumpGradient lam ρ (roomCenter ρ U j) (V j) x +
        scaledBumpGradient γ ρ (roomCenter ρ U M) (EuclideanSpace.single 0 1) x) -
      (-γ • EuclideanSpace.single 0 1 +
        ∑ j ∈ Finset.range M, scaledBumpGradient lam ρ (roomCenter ρ U j) (V j) y +
        scaledBumpGradient γ ρ (roomCenter ρ U M) (EuclideanSpace.single 0 1) y) =
      (∑ j ∈ Finset.range M, scaledBumpGradient lam ρ (roomCenter ρ U j) (V j) x -
        ∑ j ∈ Finset.range M, scaledBumpGradient lam ρ (roomCenter ρ U j) (V j) y) +
      (scaledBumpGradient γ ρ (roomCenter ρ U M) (EuclideanSpace.single 0 1) x -
        scaledBumpGradient γ ρ (roomCenter ρ U M) (EuclideanSpace.single 0 1) y) := by abel
  rw [heq]
  calc
    _ ≤ _ + _ := norm_add_le _ _
    _ ≤ (lam / ρ * bumpConstant * B) * ‖x - y‖ +
        (γ / ρ * (10 * radialProfileBound)) * ‖x - y‖ := add_le_add hs ht
    _ = _ := by unfold bumpConstant; ring

theorem chainValue_gradient_lower_outside_terminal {n M : ℕ} {ρ γ lam B : ℝ}
    (hρ : 0 < ρ) (hγ : 0 ≤ γ) (hlam : 0 ≤ lam) (hB : 0 ≤ B)
    (U V : ℕ → Space n) (hU : ∀ i, U i 0 = 0)
    (hV : ∀ i < M, ‖V i‖ ≤ B) (x : Space n)
    (hx : x ∉ closedBall (roomCenter ρ U M) ρ) :
    γ - lam * bumpConstant * B ≤
      ‖gradient (chainValue M ρ γ lam (roomCenter ρ U) V) x‖ := by
  have hs := room_gradient_sum_bound hρ hlam hB U V hU hV x
  have hc : ‖(-γ) • (EuclideanSpace.single 0 1 : Space n)‖ = γ := by
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hγ, EuclideanSpace.norm_single]
    simp
  rw [chainValue_gradient M hρ γ lam]
  unfold chainGradient
  rw [scaledBumpGradient_zero_off γ hρ _ _ x hx, add_zero]
  have ht := norm_sub_le
    ((-γ) • EuclideanSpace.single 0 1 +
      ∑ j ∈ Finset.range M, scaledBumpGradient lam ρ (roomCenter ρ U j) (V j) x)
    (∑ j ∈ Finset.range M, scaledBumpGradient lam ρ (roomCenter ρ U j) (V j) x)
  rw [add_sub_cancel_right, hc] at ht
  linarith

/-- Equation (7.11), for the actual cutoff and centers: every sufficiently
stationary point is in the terminal room. -/
theorem stationary_point_in_terminal_room {n M : ℕ} {ρ η : ℝ}
    (hρ : 0 < ρ) (hη : 0 < η) (U : ℕ → Space n)
    (hU : ∀ i, U i 0 = 0) (hgood : ∀ i < M, ‖U i‖ ≤ 2)
    (x : Space n)
    (hx : ‖gradient (chainValue M ρ (4 * η) ((4 * η) / (16 * bumpConstant))
      (roomCenter ρ U) U) x‖ ≤ η) :
    x ∈ closedBall (roomCenter ρ U M) ρ := by
  by_contra hout
  have hC := bumpConstant_pos
  have hb := chainValue_gradient_lower_outside_terminal hρ (by positivity : 0 ≤ 4 * η)
    (by positivity : 0 ≤ (4 * η) / (16 * bumpConstant)) (by norm_num : (0 : ℝ) ≤ 2)
    U U hU hgood x hout
  have heq : (4 * η) / (16 * bumpConstant) * bumpConstant * 2 = η / 2 := by
    field_simp
    ring
  rw [heq] at hb
  linarith

end NCBall
