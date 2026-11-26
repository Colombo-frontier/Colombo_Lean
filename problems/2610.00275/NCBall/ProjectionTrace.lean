import NCBall.ReusablePolicy

/-! # Cumulative covariance loss for the actual reusable-handle posterior -/

noncomputable section
open scoped InnerProductSpace BigOperators
namespace NCBall

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem residualProjection_inner_self {Q : E →L[ℝ] E} (hQ : IsResidualProjection Q) (x : E) :
    ⟪x, Q x⟫_ℝ = ‖Q x‖ ^ 2 := by
  have he := hQ.2 x (Q x)
  simpa only [hQ.1, real_inner_self_eq_norm_sq] using he.symm

theorem rankProjection_inner_normalized (b x : E) :
    ⟪x, rankProjection b x⟫_ℝ = ⟪‖b‖⁻¹ • b, x⟫_ℝ ^ 2 := by
  by_cases hb : b = 0
  · simp [hb, rankProjection_apply]
  have hn : ‖b‖ ≠ 0 := norm_ne_zero_iff.mpr hb
  rw [rankProjection_apply, real_inner_smul_right, real_inner_smul_left, real_inner_comm x b]
  field_simp
  ring

theorem residualUpdate_norm_sq {Q : E →L[ℝ] E} (hQ : IsResidualProjection Q) (a x : E) :
    ‖residualUpdate Q a x‖ ^ 2 =
      ‖Q x‖ ^ 2 - ⟪normalizedInnovation Q a, x⟫_ℝ ^ 2 := by
  rw [← residualProjection_inner_self (residualUpdate_isProjection hQ a)]
  change ⟪x, Q x - rankProjection (Q a) x⟫_ℝ = _
  rw [inner_sub_right, residualProjection_inner_self hQ, rankProjection_inner_normalized]
  rfl

theorem handleBlock_inner_apply {H : ℕ} (i : Fin (H + 1)) (a : F) (x : HandleLatent F H) :
    ⟪handleBlock F i a, x⟫_ℝ = ⟪a, x i⟫_ℝ := by
  classical
  rw [PiLp.inner_apply]
  rw [Finset.sum_eq_single i]
  · simp [handleBlock]
  · intro j _ hji
    simp [handleBlock, Pi.single_apply, hji]
  · simp

def hiddenVarianceLoss {n H : ℕ} (b : OrthonormalBasis (Fin n) ℝ F)
    (Q : HandleLatent F H →L[ℝ] HandleLatent F H) : ℝ :=
  n - ∑ i, ‖Q (handleBlock F 0 (b i))‖ ^ 2

theorem hiddenVarianceLoss_zero {n H : ℕ} (b : OrthonormalBasis (Fin n) ℝ F) :
    hiddenVarianceLoss b (ContinuousLinearMap.id ℝ (HandleLatent F H)) = 0 := by
  simp [hiddenVarianceLoss, handleBlock_norm, b.orthonormal.norm_eq_one]

theorem hiddenVarianceLoss_update {n H : ℕ} (b : OrthonormalBasis (Fin n) ℝ F)
    {Q : HandleLatent F H →L[ℝ] HandleLatent F H} (hQ : IsResidualProjection Q)
    (a : HandleLatent F H) :
    hiddenVarianceLoss b (residualUpdate Q a) = hiddenVarianceLoss b Q +
      ‖hiddenBlock F H (normalizedInnovation Q a)‖ ^ 2 := by
  have he : (∑ i, ⟪normalizedInnovation Q a, handleBlock F 0 (b i)⟫_ℝ ^ 2) =
      ‖hiddenBlock F H (normalizedInnovation Q a)‖ ^ 2 := by
    have hc (i : Fin n) : ⟪normalizedInnovation Q a, handleBlock F 0 (b i)⟫_ℝ =
        ⟪b i, hiddenBlock F H (normalizedInnovation Q a)⟫_ℝ := by
      rw [real_inner_comm, handleBlock_inner_apply]
      rfl
    simp_rw [hc]
    simpa only [Real.norm_eq_abs, sq_abs] using
      b.sum_sq_norm_inner (hiddenBlock F H (normalizedInnovation Q a))
  simp only [hiddenVarianceLoss, residualUpdate_norm_sq hQ, Finset.sum_sub_distrib]
  rw [he]
  ring

variable {S : Type*} [MeasurableSpace S]
  [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]

/-- The trace deficit is bounded for every recorded history. The posterior
itself is the actual conditional Gaussian law from `AdaptivePosterior`. -/
theorem reusable_posterior_trace_loss {n H : ℕ} (b : OrthonormalBasis (Fin n) ℝ F)
    (p : ReusableQueryPolicy S F H) (σ : ℝ) (hσ : 0 < σ)
    (t : ℕ) (h : LinearHistory S t) :
    hiddenVarianceLoss b (linearPosteriorProjection (p.toLinear σ) t h) ≤ t / σ ^ 2 := by
  induction t with
  | zero => simp [linearPosteriorProjection, hiddenVarianceLoss_zero]
  | succ t ih =>
    change hiddenVarianceLoss b (residualUpdate (linearPosteriorProjection (p.toLinear σ) t h.1)
      ((p.toLinear σ).query t h.1)) ≤ _
    rw [hiddenVarianceLoss_update b (linearPosteriorProjection_isProjection _ _ _)]
    have ht := ih h.1
    have hs := reusable_query_innovation_bound p σ hσ t h.1
    push_cast
    rw [add_div]
    linarith

end NCBall
