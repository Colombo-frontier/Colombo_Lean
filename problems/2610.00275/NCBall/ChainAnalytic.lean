import NCBall.Construction
import NCBall.ScaledBump

/-! # Analytic verification for the actual hidden-room sum -/

noncomputable section
open Set Metric Filter InnerProductSpace
open scoped BigOperators InnerProductSpace NNReal ContDiff
namespace NCBall

def chainGradient {n : ℕ} (M : ℕ) (ρ γ lam : ℝ) (c V : ℕ → Space n) (x : Space n) : Space n :=
  (-γ) • EuclideanSpace.single 0 1 +
    ∑ j ∈ Finset.range M, scaledBumpGradient lam ρ (c j) (V j) x +
    scaledBumpGradient γ ρ (c M) (EuclideanSpace.single 0 1) x

theorem terminalBump_eq_radialLinearBump {n : ℕ} (y : Space n) :
    terminalBump y = radialLinearBump (EuclideanSpace.single 0 1) y := by
  simp [terminalBump, radialLinearBump, cutoff, EuclideanSpace.inner_single_left]

theorem chainValue_decompose {n : ℕ} (M : ℕ) (ρ γ lam : ℝ) (c V : ℕ → Space n) (x : Space n) :
    chainValue M ρ γ lam c V x = -γ * x 0 +
      ∑ j ∈ Finset.range M, scaledBump lam ρ (c j) (V j) x +
      scaledBump γ ρ (c M) (EuclideanSpace.single 0 1) x := by
  simp only [chainValue, scaledBump, terminalBump_eq_radialLinearBump, Finset.mul_sum]
  rfl

theorem carrier_hasGradientAt {n : ℕ} (γ : ℝ) (x : Space n) :
    HasGradientAt (fun y : Space n => -γ * y 0) ((-γ) • EuclideanSpace.single 0 1) x := by
  have h := ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin (n + 1)) 0).hasFDerivAt (x := x)).const_mul (-γ)
  change HasFDerivAt _ (toDual ℝ (Space n) ((-γ) • EuclideanSpace.single 0 1)) x
  convert h using 1
  ext y
  simp [EuclideanSpace.inner_single_left, inner_smul_left]

theorem chainValue_hasGradientAt {n : ℕ} (M : ℕ) {ρ : ℝ} (hρ : 0 < ρ)
    (γ lam : ℝ) (c V : ℕ → Space n) (x : Space n) :
    HasGradientAt (chainValue M ρ γ lam c V) (chainGradient M ρ γ lam c V x) x := by
  have hs := hasGradientAt_finset_sum (Finset.range M)
    (fun j => scaledBump lam ρ (c j) (V j))
    (fun j => scaledBumpGradient lam ρ (c j) (V j) x) x
    (fun j _ => scaledBump_hasGradientAt lam hρ (c j) (V j) x)
  have h := hasGradientAt_add _ _ _ _ x
    (hasGradientAt_add _ _ _ _ x (carrier_hasGradientAt γ x) hs)
    (scaledBump_hasGradientAt γ hρ (c M) (EuclideanSpace.single 0 1) x)
  convert h using 1
  ext y
  exact chainValue_decompose M ρ γ lam c V y

theorem chainValue_gradient {n : ℕ} (M : ℕ) {ρ : ℝ} (hρ : 0 < ρ)
    (γ lam : ℝ) (c V : ℕ → Space n) (x : Space n) :
    gradient (chainValue M ρ γ lam c V) x = chainGradient M ρ γ lam c V x :=
  (chainValue_hasGradientAt M hρ γ lam c V x).gradient

theorem room_gradient_sum_bound {n M : ℕ} {ρ lam B : ℝ}
    (hρ : 0 < ρ) (hlam : 0 ≤ lam) (hB : 0 ≤ B)
    (U V : ℕ → Space n) (hU : ∀ i, U i 0 = 0)
    (hV : ∀ i < M, ‖V i‖ ≤ B) (x : Space n) :
    ‖∑ j ∈ Finset.range M, scaledBumpGradient lam ρ (roomCenter ρ U j) (V j) x‖ ≤
      lam * bumpConstant * B := by
  have hC := bumpConstant_pos
  apply norm_sum_disjoint_support (Finset.range M)
    (fun j => closedBall (roomCenter ρ U j) ρ) _ x (by positivity)
  · intro i hi j hj hij
    exact rooms_disjoint hρ U hU hij
  · intro i hi hx
    exact scaledBumpGradient_zero_off lam hρ (roomCenter ρ U i) (V i) x hx
  · intro i hi
    exact (scaledBumpGradient_bound_C hlam _ _ _).trans
      (mul_le_mul_of_nonneg_left (hV i (Finset.mem_range.mp hi))
        (mul_nonneg hlam bumpConstant_pos.le))

theorem chainValue_gradient_bound {n M : ℕ} {ρ γ lam B : ℝ}
    (hρ : 0 < ρ) (hγ : 0 ≤ γ) (hlam : 0 ≤ lam) (hB : 0 ≤ B)
    (U V : ℕ → Space n) (hU : ∀ i, U i 0 = 0)
    (hV : ∀ i < M, ‖V i‖ ≤ B) (x : Space n) :
    ‖gradient (chainValue M ρ γ lam (roomCenter ρ U) V) x‖ ≤
      γ + lam * bumpConstant * B + γ * bumpConstant := by
  have hs := room_gradient_sum_bound hρ hlam hB U V hU hV x
  have ht := scaledBumpGradient_bound_C (ρ := ρ) hγ (roomCenter ρ U M)
    (EuclideanSpace.single 0 1) x
  simp only [EuclideanSpace.norm_single, norm_one, mul_one] at ht
  have hc : ‖(-γ) • (EuclideanSpace.single 0 1 : Space n)‖ = γ := by
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hγ, EuclideanSpace.norm_single]
    simp
  rw [chainValue_gradient M hρ γ lam]
  unfold chainGradient
  exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (by linarith)) ht)

theorem chainValue_lipschitz {n M : ℕ} {ρ γ lam B : ℝ}
    (hρ : 0 < ρ) (hγ : 0 ≤ γ) (hlam : 0 ≤ lam) (hB : 0 ≤ B)
    (U V : ℕ → Space n) (hU : ∀ i, U i 0 = 0)
    (hV : ∀ i < M, ‖V i‖ ≤ B) :
    LipschitzWith ⟨γ + lam * bumpConstant * B + γ * bumpConstant, by
      have := bumpConstant_pos
      positivity⟩ (chainValue M ρ γ lam (roomCenter ρ U) V) := by
  apply lipschitzWith_of_nnnorm_fderiv_le ((chainValue_smooth _ _ _ _ _ _).differentiable (by simp))
  intro x
  have hb := chainValue_gradient_bound hρ hγ hlam hB U V hU hV x
  rw [chainValue_gradient M hρ γ lam] at hb
  rw [(chainValue_hasGradientAt M hρ γ lam (roomCenter ρ U) V x).hasFDerivAt.fderiv]
  change ‖toDual ℝ (Space n) (chainGradient M ρ γ lam (roomCenter ρ U) V x)‖ ≤ _
  rwa [(toDual ℝ (Space n)).norm_map]

end NCBall
