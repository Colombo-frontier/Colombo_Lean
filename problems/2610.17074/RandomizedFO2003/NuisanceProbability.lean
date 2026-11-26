import RandomizedFO2003.BlockDirections

namespace RandomizedFO2003.SpectralCoordinates

open MeasureTheory Spherical
open scoped BigOperators

variable {J : ℕ}

theorem block_family_projection_tail (K : Fin J → ℕ) (hK : ∀ j, 0 < K j)
    (W : (j : Fin J) → Submodule ℝ (ComponentSpace K j)) (T : ℕ)
    (hdim : ∀ j, Module.finrank ℝ (W j) ≤ T) (η : ℝ) (hη : 0 < η) :
    sphereLaw (BlockSpace K) {u | ∃ j,
      η ≤ ‖(W j).orthogonalProjection (blockDirection K j u)‖} ≤
      ∑ j, ENNReal.ofReal ((T : ℝ) / ((K j : ℝ) * η ^ 2)) := by
  calc
    _ = sphereLaw (BlockSpace K) (⋃ j, {u |
        η ≤ ‖(W j).orthogonalProjection (blockDirection K j u)‖}) := by congr 1; ext u; simp
    _ ≤ ∑ j, sphereLaw (BlockSpace K) {u |
        η ≤ ‖(W j).orthogonalProjection (blockDirection K j u)‖} := measure_iUnion_fintype_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j _
      apply (blockDirection_projection_tail K j (hK j) (W j) η hη).trans
      apply ENNReal.ofReal_le_ofReal
      exact div_le_div_of_nonneg_right (by exact_mod_cast hdim j)
        (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))

/-- Random nuisance subspaces may depend arbitrarily on an independent
parameter. Joint measurability is explicit; no independence is inferred from
the mere fact that a subspace is random. -/
theorem independent_nuisance_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (K : Fin J → ℕ) (hK : ∀ j, 0 < K j)
    (W : Ω → (j : Fin J) → Submodule ℝ (ComponentSpace K j))
    (hW : ∀ j, Measurable (fun p : Ω × BlockSpace K =>
      ‖(W p.1 j).orthogonalProjection (blockDirection K j p.2)‖))
    (T : ℕ) (hdim : ∀ ω j, Module.finrank ℝ (W ω j) ≤ T)
    (η : ℝ) (hη : 0 < η) :
    (μ.prod (sphereLaw (BlockSpace K))) {p | ∃ j,
      η ≤ ‖(W p.1 j).orthogonalProjection (blockDirection K j p.2)‖} ≤
      ∑ j, ENNReal.ofReal ((T : ℝ) / ((K j : ℝ) * η ^ 2)) := by
  have hset : MeasurableSet {p : Ω × BlockSpace K | ∃ j,
      η ≤ ‖(W p.1 j).orthogonalProjection (blockDirection K j p.2)‖} := by
    simp only [Set.setOf_exists]
    exact MeasurableSet.iUnion (fun j => measurableSet_le measurable_const (hW j))
  rw [Measure.prod_apply hset]
  calc
    _ ≤ ∫⁻ _ω, ∑ j, ENNReal.ofReal ((T : ℝ) / ((K j : ℝ) * η ^ 2)) ∂μ := by
      apply lintegral_mono
      intro ω
      exact block_family_projection_tail K hK (W ω) T (hdim ω) η hη
    _ = _ := by simp

theorem nuisance_tail_uniform_multiplicity (K : Fin J → ℕ) (R T : ℕ)
    (hR : 0 < R) (hK : ∀ j, R ≤ K j) (η : ℝ) (hη : 0 < η) :
    (∑ j, ENNReal.ofReal ((T : ℝ) / ((K j : ℝ) * η ^ 2))) ≤
      ENNReal.ofReal ((J : ℝ) * T / ((R : ℝ) * η ^ 2)) := by
  have hRreal : (0 : ℝ) < R := by exact_mod_cast hR
  calc
    _ ≤ ∑ _j : Fin J, ENNReal.ofReal ((T : ℝ) / ((R : ℝ) * η ^ 2)) := by
      apply Finset.sum_le_sum
      intro j _
      apply ENNReal.ofReal_le_ofReal
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg T)
        (mul_pos hRreal (sq_pos_of_pos hη))
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hK j) (sq_nonneg η))
    _ = _ := by simp [ENNReal.ofReal_mul, div_eq_mul_inv, nsmul_eq_mul, mul_assoc]

end RandomizedFO2003.SpectralCoordinates
