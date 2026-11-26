import NCBall.ProjectionTrace
import NCBall.Information
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-! # The spectral covariance bound, derived from actual residual projections -/

noncomputable section
open scoped InnerProductSpace BigOperators
namespace NCBall

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {H : ℕ}

def hiddenInjection (H : ℕ) : F →ₗ[ℝ] HandleLatent F H where
  toFun := handleBlock F 0
  map_add' := by intros; ext i; simp [handleBlock, Pi.single_add]
  map_smul' := by intros; ext i; simp [handleBlock, Pi.single_smul]

def hiddenCovariance (Q : HandleLatent F H →L[ℝ] HandleLatent F H) : F →ₗ[ℝ] F :=
  (hiddenBlock F H).toLinearMap.comp (Q.toLinearMap.comp (hiddenInjection H))

theorem hiddenCovariance_inner (Q : HandleLatent F H →L[ℝ] HandleLatent F H) (a b : F) :
    ⟪a, hiddenCovariance Q b⟫_ℝ =
      ⟪handleBlock F 0 a, Q (handleBlock F 0 b)⟫_ℝ := by
  rw [handleBlock_inner_apply]
  rfl

theorem hiddenCovariance_symmetric {Q : HandleLatent F H →L[ℝ] HandleLatent F H}
    (hQ : IsResidualProjection Q) : (hiddenCovariance Q).IsSymmetric := by
  intro a b
  calc
    ⟪hiddenCovariance Q a, b⟫_ℝ = ⟪b, hiddenCovariance Q a⟫_ℝ := real_inner_comm _ _
    _ = ⟪handleBlock F 0 b, Q (handleBlock F 0 a)⟫_ℝ := hiddenCovariance_inner Q b a
    _ = ⟪Q (handleBlock F 0 b), handleBlock F 0 a⟫_ℝ := (hQ.2 _ _).symm
    _ = ⟪handleBlock F 0 a, Q (handleBlock F 0 b)⟫_ℝ := real_inner_comm _ _
    _ = ⟪a, hiddenCovariance Q b⟫_ℝ := (hiddenCovariance_inner Q a b).symm

theorem hiddenCovariance_inner_self {Q : HandleLatent F H →L[ℝ] HandleLatent F H}
    (hQ : IsResidualProjection Q) (a : F) :
    ⟪a, hiddenCovariance Q a⟫_ℝ = ‖Q (handleBlock F 0 a)‖ ^ 2 := by
  rw [hiddenCovariance_inner, residualProjection_inner_self hQ]

variable [FiniteDimensional ℝ F]

def hiddenEigenbasis {Q : HandleLatent F H →L[ℝ] HandleLatent F H}
    (hQ : IsResidualProjection Q) : OrthonormalBasis (Fin (Module.finrank ℝ F)) ℝ F :=
  (hiddenCovariance_symmetric hQ).eigenvectorBasis rfl

def hiddenEigenvalues {Q : HandleLatent F H →L[ℝ] HandleLatent F H}
    (hQ : IsResidualProjection Q) : Fin (Module.finrank ℝ F) → ℝ :=
  (hiddenCovariance_symmetric hQ).eigenvalues rfl

theorem hiddenEigenbasis_apply {Q : HandleLatent F H →L[ℝ] HandleLatent F H}
    (hQ : IsResidualProjection Q) (i : Fin (Module.finrank ℝ F)) :
    hiddenCovariance Q (hiddenEigenbasis hQ i) =
      hiddenEigenvalues hQ i • hiddenEigenbasis hQ i :=
  (hiddenCovariance_symmetric hQ).apply_eigenvectorBasis rfl i

theorem hiddenEigenvalues_norm_sq {Q : HandleLatent F H →L[ℝ] HandleLatent F H}
    (hQ : IsResidualProjection Q) (i : Fin (Module.finrank ℝ F)) :
    hiddenEigenvalues hQ i = ‖Q (handleBlock F 0 (hiddenEigenbasis hQ i))‖ ^ 2 := by
  have he := hiddenCovariance_inner_self hQ (hiddenEigenbasis hQ i)
  rw [hiddenEigenbasis_apply hQ, real_inner_smul_right, real_inner_self_eq_norm_sq,
    (hiddenEigenbasis hQ).norm_eq_one, one_pow, mul_one] at he
  exact he

theorem hiddenEigenvalues_mem_unit {Q : HandleLatent F H →L[ℝ] HandleLatent F H}
    (hQ : IsResidualProjection Q) (i : Fin (Module.finrank ℝ F)) :
    0 ≤ hiddenEigenvalues hQ i ∧ hiddenEigenvalues hQ i ≤ 1 := by
  rw [hiddenEigenvalues_norm_sq]
  refine ⟨sq_nonneg _, ?_⟩
  have hn := residualProjection_norm_le hQ (handleBlock F 0 (hiddenEigenbasis hQ i))
  rw [handleBlock_norm, (hiddenEigenbasis hQ).norm_eq_one] at hn
  nlinarith [norm_nonneg (Q (handleBlock F 0 (hiddenEigenbasis hQ i)))]

theorem hidden_eigenrows_orthogonal {Q : HandleLatent F H →L[ℝ] HandleLatent F H}
    (hQ : IsResidualProjection Q) (i j : Fin (Module.finrank ℝ F)) (hij : i ≠ j) :
    ⟪Q (handleBlock F 0 (hiddenEigenbasis hQ i)),
      Q (handleBlock F 0 (hiddenEigenbasis hQ j))⟫_ℝ = 0 := by
  rw [hQ.2, hQ.1, ← hiddenCovariance_inner, hiddenEigenbasis_apply hQ,
    real_inner_smul_right, (hiddenEigenbasis hQ).orthonormal.2 hij, mul_zero]

theorem hidden_trace_eigenvalues {Q : HandleLatent F H →L[ℝ] HandleLatent F H}
    (hQ : IsResidualProjection Q) :
    ∑ i, (1 - hiddenEigenvalues hQ i) = hiddenVarianceLoss (hiddenEigenbasis hQ) Q := by
  simp [hiddenVarianceLoss, Finset.sum_sub_distrib, hiddenEigenvalues_norm_sq]

variable {S : Type*} [MeasurableSpace S] [MeasurableSpace F] [BorelSpace F]

omit [MeasurableSpace S] [MeasurableSpace F] [BorelSpace F] in
theorem hidden_many_large_variances {Q : HandleLatent F H →L[ℝ] HandleLatent F H}
    (hQ : IsResidualProjection Q)
    (ht : hiddenVarianceLoss (hiddenEigenbasis hQ) Q < (Module.finrank ℝ F : ℝ) / 16) :
    3 * (Module.finrank ℝ F : ℝ) / 4 ≤
      ((Finset.univ.filter (fun i => 3 / 4 ≤ hiddenEigenvalues hQ i)).card : ℝ) := by
  classical
  have hs : (∑ i, (1 - hiddenEigenvalues hQ i)) < (Module.finrank ℝ F : ℝ) * 1 / 16 := by
    rw [hidden_trace_eigenvalues]
    simpa using ht
  have hc := many_small_eigenvalues (fun i => 1 - hiddenEigenvalues hQ i)
    (by norm_num : (0 : ℝ) < 1) (fun i => sub_nonneg.mpr (hiddenEigenvalues_mem_unit hQ i).2) hs
  have he : (Finset.univ.filter (fun i => 1 - hiddenEigenvalues hQ i ≤ 1 / 4)) =
      (Finset.univ.filter (fun i => 3 / 4 ≤ hiddenEigenvalues hQ i)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor <;> intro hi <;> linarith
  rwa [he] at hc

theorem reusable_posterior_many_large_variances (p : ReusableQueryPolicy S F H)
    (σ : ℝ) (hσ : 0 < σ) (t : ℕ) (h : LinearHistory S t)
    (ht : (t : ℝ) < (Module.finrank ℝ F : ℝ) * σ ^ 2 / 16) :
    let hQ := linearPosteriorProjection_isProjection (p.toLinear σ) t h
    3 * (Module.finrank ℝ F : ℝ) / 4 ≤
      ((Finset.univ.filter (fun i => 3 / 4 ≤ hiddenEigenvalues hQ i)).card : ℝ) := by
  classical
  dsimp only
  let hQ := linearPosteriorProjection_isProjection (p.toLinear σ) t h
  have htrace := reusable_posterior_trace_loss (hiddenEigenbasis hQ) p σ hσ t h
  have hdiv : (t : ℝ) / σ ^ 2 < (Module.finrank ℝ F : ℝ) / 16 :=
    (div_lt_iff₀ (sq_pos_of_pos hσ)).mpr (by nlinarith)
  exact hidden_many_large_variances hQ (htrace.trans_lt hdiv)

end NCBall
