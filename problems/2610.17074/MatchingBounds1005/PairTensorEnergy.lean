import MatchingBounds1005.TensorCoordinateEnergy

/-! The actual two physical channel variances in the stopped-signal KL budget,
with no factor equal to the number of oracle calls. -/
noncomputable section
open scoped BigOperators InnerProductSpace

namespace MatchingBounds1005.TensorGeometry
open GaussianVector TensorChannelRows GaussianBlockProjection AdaptiveGaussian

def stoppedCoordinates {ι : Type*} {d : ℕ} (k : ℕ) (signals : Finset ι)
    (b : ι → Vec d) (w : ℝ) (ell : ι → ℕ) (t : ℕ) :=
  w • ∑ s ∈ signals, if t < ell s then tensorCoordinates d k (rankOne k (b s)) else 0

theorem stoppedCoordinates_norm_le {ι : Type*} {d : ℕ} (k : ℕ) (signals : Finset ι)
    (b : ι → Vec d) (hb : ∀ s ∈ signals, ‖b s‖ = 1) (w : ℝ) (ell : ι → ℕ) (t : ℕ) :
    ‖stoppedCoordinates k signals b w ell t‖ ≤ |w| * signals.card := by
  unfold stoppedCoordinates
  rw [norm_smul, Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg w)
  calc
    _ ≤ ∑ s ∈ signals, ‖if t < ell s then tensorCoordinates d k (rankOne k (b s)) else 0‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _s ∈ signals, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro s hs
      split_ifs
      · simp only [LinearIsometryEquiv.norm_map, rankOne_norm, hb s hs, one_pow, le_refl]
      · simp
    _ = _ := by simp

theorem normalizedSignal_norm_energy {d : ℕ} (σ₃ σ₄ : ℝ)
    (S₃ : Vec (cubicDim d)) (S₄ : Vec (quarticDim d)) :
    ‖normalizedSignal σ₃ σ₄ S₃ S₄‖ ^ 2 / 2 =
      ‖S₃‖ ^ 2 / (2 * σ₃ ^ 2) + ‖S₄‖ ^ 2 / (2 * σ₄ ^ 2) := by
  have h := inner_split (cubicDim d) (quarticDim d)
    (normalizedSignal σ₃ σ₄ S₃ S₄) (normalizedSignal σ₃ σ₄ S₃ S₄)
  simp only [real_inner_self_eq_norm_sq, normalizedSignal,
    LinearEquiv.apply_symm_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inv_pow] at h
  rw [show ‖normalizedSignal σ₃ σ₄ S₃ S₄‖ ^ 2 =
    (σ₃ ^ 2)⁻¹ * ‖S₃‖ ^ 2 + (σ₄ ^ 2)⁻¹ * ‖S₄‖ ^ 2 from h]
  ring

theorem stopped_pair_norm_energy {ι : Type*} {d : ℕ}
    (signals : Finset ι) (b : ι → Vec d) (hb : ∀ s ∈ signals, ‖b s‖ = 1)
    (w₃ w₄ σ₃ σ₄ : ℝ) (ell : ι → ℕ) (t : ℕ) :
    ‖normalizedSignal σ₃ σ₄ (stoppedCoordinates 3 signals b w₃ ell t)
      (stoppedCoordinates 4 signals b w₄ ell t)‖ ^ 2 / 2 ≤
      (signals.card : ℝ) ^ 2 * w₃ ^ 2 / (2 * σ₃ ^ 2) +
      (signals.card : ℝ) ^ 2 * w₄ ^ 2 / (2 * σ₄ ^ 2) := by
  rw [normalizedSignal_norm_energy]
  have hsq (k : ℕ) (w : ℝ) : ‖stoppedCoordinates k signals b w ell t‖ ^ 2 ≤
      (signals.card : ℝ) ^ 2 * w ^ 2 := by
    have h := pow_le_pow_left₀ (norm_nonneg _) (stoppedCoordinates_norm_le k signals b hb w ell t) 2
    simpa only [mul_pow, sq_abs, mul_comm] using h
  exact add_le_add (div_le_div_of_nonneg_right (hsq 3 w₃) (by positivity))
    (div_le_div_of_nonneg_right (hsq 4 w₄) (by positivity))

attribute [local irreducible] Submodule.orthogonalProjection projection

theorem cumulative_pair_coordinate_energy {ι : Type*} {d : ℕ}
    (signals : Finset ι) (b : ι → Vec d) (hb : ∀ s ∈ signals, ‖b s‖ = 1)
    (V₃ : ℕ → Submodule ℝ (Vec (cubicDim d))) (hV₃ : Monotone V₃)
    (V₄ : ℕ → Submodule ℝ (Vec (quarticDim d))) (hV₄ : Monotone V₄)
    (W : ι → Submodule ℝ (Vec d)) (ell : ι → ℕ) (T : ℕ)
    (hell : ∀ s ∈ signals, ell s ≤ T)
    (hobs₃ : ∀ s ∈ signals, V₃ (ell s) ≤ coordinateObservation 3 (W s))
    (hobs₄ : ∀ s ∈ signals, V₄ (ell s) ≤ coordinateObservation 4 (W s))
    (w₃ w₄ σ₃ σ₄ θ : ℝ) (hθ : 0 ≤ θ)
    (hangle : ∀ s ∈ signals, ‖(W s).orthogonalProjection (b s)‖ ≤ θ) :
    (∑ t ∈ Finset.range T,
      ‖projection (blockSpace (V₃ (t + 1)) (V₄ (t + 1)) ⊓
          (blockSpace (V₃ t) (V₄ t))ᗮ)
        (normalizedSignal σ₃ σ₄ (stoppedCoordinates 3 signals b w₃ ell t)
          (stoppedCoordinates 4 signals b w₄ ell t))‖ ^ 2 / 2) ≤
      3 * (signals.card : ℝ) ^ 2 * w₃ ^ 2 * θ ^ 4 / (2 * σ₃ ^ 2) +
      4 * (signals.card : ℝ) ^ 2 * w₄ ^ 2 * θ ^ 6 / (2 * σ₄ ^ 2) := by
  simp_rw [TensorJointEnergy.normalized_innovation_energy]
  rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div]
  have h₃ := cumulative_coordinate_rankOne_energy (k := 3) (by norm_num) signals b hb V₃ hV₃
    W ell T hell hobs₃ w₃ θ hθ hangle
  have h₄ := cumulative_coordinate_rankOne_energy (k := 4) (by norm_num) signals b hb V₄ hV₄
    W ell T hell hobs₄ w₄ θ hθ hangle
  apply add_le_add
  · apply div_le_div_of_nonneg_right _ (by positivity)
    simpa only [projection, InnovationEnergy.proj, stoppedCoordinates, Nat.reduceSub,
      Nat.reduceMul, Nat.cast_ofNat] using h₃
  · apply div_le_div_of_nonneg_right _ (by positivity)
    simpa only [projection, InnovationEnergy.proj, stoppedCoordinates, Nat.reduceSub,
      Nat.reduceMul, Nat.cast_ofNat] using h₄

theorem cumulative_pair_global_energy {ι : Type*} {d : ℕ}
    (signals : Finset ι) (b : ι → Vec d) (hb : ∀ s ∈ signals, ‖b s‖ = 1)
    (V₃ : ℕ → Submodule ℝ (Vec (cubicDim d))) (hV₃ : Monotone V₃)
    (V₄ : ℕ → Submodule ℝ (Vec (quarticDim d))) (hV₄ : Monotone V₄)
    (W : ι → Submodule ℝ (Vec d)) (ell : ι → ℕ) (T : ℕ)
    (hell : ∀ s ∈ signals, ell s ≤ T)
    (hobs₃ : ∀ s ∈ signals, V₃ (ell s) ≤ coordinateObservation 3 (W s))
    (hobs₄ : ∀ s ∈ signals, V₄ (ell s) ≤ coordinateObservation 4 (W s))
    (w₃ w₄ σ₃ σ₄ : ℝ) :
    (∑ t ∈ Finset.range T,
      ‖projection (blockSpace (V₃ (t + 1)) (V₄ (t + 1)) ⊓
          (blockSpace (V₃ t) (V₄ t))ᗮ)
        (normalizedSignal σ₃ σ₄ (stoppedCoordinates 3 signals b w₃ ell t)
          (stoppedCoordinates 4 signals b w₄ ell t))‖ ^ 2 / 2) ≤
      3 * (signals.card : ℝ) ^ 2 * w₃ ^ 2 / (2 * σ₃ ^ 2) +
      4 * (signals.card : ℝ) ^ 2 * w₄ ^ 2 / (2 * σ₄ ^ 2) := by
  have ha (s : ι) (hs : s ∈ signals) : ‖(W s).orthogonalProjection (b s)‖ ≤ (1 : ℝ) := by
    calc
      _ ≤ ‖(W s).orthogonalProjection‖ * ‖b s‖ := (W s).orthogonalProjection.le_opNorm _
      _ ≤ 1 * ‖b s‖ := mul_le_mul_of_nonneg_right (W s).orthogonalProjection_norm_le (norm_nonneg _)
      _ = 1 := by rw [hb s hs, mul_one]
  simpa only [one_pow, mul_one] using cumulative_pair_coordinate_energy signals b hb V₃ hV₃ V₄ hV₄
    W ell T hell hobs₃ hobs₄ w₃ w₄ σ₃ σ₄ 1 (by norm_num) ha

end MatchingBounds1005.TensorGeometry
