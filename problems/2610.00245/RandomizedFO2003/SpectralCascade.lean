import RandomizedFO2003.CascadeParameters
import RandomizedFO2003.ContinuousSpectralMoments

namespace RandomizedFO2003.FiniteSpectralDesign

open SpectralCoordinates Cascade

variable {m : ℕ} {γ L : ℝ} (S : FiniteSpectralDesign m γ L (1 / (16 * γ)))

/-- The actual static cascade from the source's spectral design. All scalar
constants are fixed before the rotations and right-hand sides are chosen. -/
noncomputable def cascade (K : Fin S.size → ℕ) (N : ℕ)
    (U : Fin (N + 1) → BlockSpace K ≃ₗᵢ[ℝ] BlockSpace K)
    (u : Fin (N + 1) → BlockSpace K) (h : ℝ) : Cascade.Data N (BlockSpace K) where
  A i := continuousConjugation (U i) (continuousDiagonal K S.node)
  a i := U i (direction K (u i) S.residual)
  b i := U i (h • u i)
  B := radiusCoefficient * h / γ
  α := h / (64 * γ)
  D := h ^ 2 / γ
  C₀ := forcingOffset
  K := saturationThreshold

noncomputable def cascadeInverse (K : Fin S.size → ℕ) (N : ℕ)
    (U : Fin (N + 1) → BlockSpace K ≃ₗᵢ[ℝ] BlockSpace K) :
    Fin (N + 1) → BlockSpace K →L[ℝ] BlockSpace K :=
  fun i => continuousConjugation (U i) (continuousDiagonal K (fun j => (S.node j)⁻¹))

theorem cascade_operator_selfAdjoint (K : Fin S.size → ℕ) (N : ℕ)
    (U : Fin (N + 1) → BlockSpace K ≃ₗᵢ[ℝ] BlockSpace K)
    (u : Fin (N + 1) → BlockSpace K) (h : ℝ) (i : Fin (N + 1)) :
    IsSelfAdjoint ((S.cascade K N U u h).A i) :=
  continuousConjugation_selfAdjoint _ _ (continuousDiagonal_selfAdjoint K S.node)

theorem cascadeInverse_selfAdjoint (K : Fin S.size → ℕ) (N : ℕ)
    (U : Fin (N + 1) → BlockSpace K ≃ₗᵢ[ℝ] BlockSpace K) (i : Fin (N + 1)) :
    IsSelfAdjoint (S.cascadeInverse K N U i) :=
  continuousConjugation_selfAdjoint _ _ (continuousDiagonal_selfAdjoint K _)

theorem cascadeInverse_left (hγ : 0 < γ) (K : Fin S.size → ℕ) (N : ℕ)
    (U : Fin (N + 1) → BlockSpace K ≃ₗᵢ[ℝ] BlockSpace K)
    (u : Fin (N + 1) → BlockSpace K) (h : ℝ) (i : Fin (N + 1)) (x : BlockSpace K) :
    S.cascadeInverse K N U i ((S.cascade K N U u h).A i x) = x :=
  continuousConjugation_inverse_left _ _ _
    (continuousDiagonal_inverse_left K S.node (fun j => (hγ.trans_le (S.node_mem j).1).ne')) x

theorem cascadeInverse_norm_le (hγ : 0 < γ) (K : Fin S.size → ℕ) (N : ℕ)
    (U : Fin (N + 1) → BlockSpace K ≃ₗᵢ[ℝ] BlockSpace K) (i : Fin (N + 1)) :
    ‖S.cascadeInverse K N U i‖ ≤ γ⁻¹ :=
  (continuousConjugation_norm_le _ _).trans
    (continuousDiagonal_inverse_norm_le K S.node hγ (fun j => (S.node_mem j).1))

theorem cascade_coercive (K : Fin S.size → ℕ) (N : ℕ)
    (U : Fin (N + 1) → BlockSpace K ≃ₗᵢ[ℝ] BlockSpace K)
    (u : Fin (N + 1) → BlockSpace K) (h : ℝ) (i : Fin (N + 1)) (x : BlockSpace K) :
    γ * ‖x‖ ≤ ‖(S.cascade K N U u h).A i x‖ :=
  continuousConjugation_coercive _ _ γ
    (continuousDiagonal_coercive K S.node γ (fun j => (S.node_mem j).1)) x

theorem cascade_quadratic_nonneg (hγ : 0 ≤ γ) (K : Fin S.size → ℕ) (N : ℕ)
    (U : Fin (N + 1) → BlockSpace K ≃ₗᵢ[ℝ] BlockSpace K)
    (u : Fin (N + 1) → BlockSpace K) (h : ℝ) (i : Fin (N + 1)) (x : BlockSpace K) :
    0 ≤ inner (𝕜 := ℝ) x ((S.cascade K N U u h).A i x) :=
  continuousConjugation_nonneg _ _
    (continuousDiagonal_nonneg K S.node (fun j => hγ.trans (S.node_mem j).1)) x

theorem cascade_operator_norm_le (hγ : 0 ≤ γ) (hL : 0 ≤ L) (K : Fin S.size → ℕ) (N : ℕ)
    (U : Fin (N + 1) → BlockSpace K ≃ₗᵢ[ℝ] BlockSpace K)
    (u : Fin (N + 1) → BlockSpace K) (h : ℝ) (i : Fin (N + 1)) :
    ‖(S.cascade K N U u h).A i‖ ≤ L := by
  apply (continuousConjugation_norm_le _ _).trans
  apply continuousDiagonal_norm_le K S.node hL
  intro j
  rw [abs_of_nonneg (hγ.trans (S.node_mem j).1)]
  exact (S.node_mem j).2

/-- Initial-gap control holds for every realization, without the good-weight
event or unit-vector hypotheses. -/
theorem cascade_initial_gap_bound (hγ : 0 < γ) (K : Fin S.size → ℕ) (N : ℕ)
    (U : Fin (N + 1) → BlockSpace K ≃ₗᵢ[ℝ] BlockSpace K)
    (u : Fin (N + 1) → BlockSpace K) (h : ℝ) (z : BlockProduct (N + 1) (BlockSpace K)) :
    (S.cascade K N U u h).energy 0 - (S.cascade K N U u h).energy z ≤
      ((N + 1 : ℕ) : ℝ) * forcingAmplitude * (h ^ 2 / γ) := by
  have hp := (S.cascade K N U u h).initial_gap_bound
    (S.cascade_quadratic_nonneg hγ.le K N U u h)
    (by change 0 ≤ h ^ 2 / γ; positivity)
    (by norm_num [cascade, saturationThreshold])
    (by norm_num [cascade, saturationThreshold, forcingOffset]) z
  convert hp using 1
  dsimp only [cascade]
  unfold forcingAmplitude forcingOffset saturationThreshold
  ring

end RandomizedFO2003.FiniteSpectralDesign
