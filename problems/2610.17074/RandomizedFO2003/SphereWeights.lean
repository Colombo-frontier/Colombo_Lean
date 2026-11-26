import RandomizedFO2003.SphereProjection
import RandomizedFO2003.MultiplicityChoice

namespace RandomizedFO2003.Spherical

open MeasureTheory SpectralCoordinates
open scoped BigOperators

variable {J : ℕ}

def coordinateSet (K : Fin J → ℕ) (j : Fin J) : Finset (Σ j, Fin (K j)) :=
  Finset.univ.map (Function.Embedding.sigmaMk j)

@[simp] theorem coordinateSet_card (K : Fin J → ℕ) (j : Fin J) :
    (coordinateSet K j).card = K j := by simp [coordinateSet]

theorem weight_eq_projectionMass (K : Fin J → ℕ) (j : Fin J) (u : BlockSpace K) :
    weight K u j = projectionMass (EuclideanSpace.basisFun (Σ j, Fin (K j)) ℝ)
      (coordinateSet K j) u := by
  have hi (i : Σ j, Fin (K j)) :
      inner (𝕜 := ℝ) (EuclideanSpace.basisFun (Σ j, Fin (K j)) ℝ i) u = u i :=
    ((EuclideanSpace.basisFun (Σ j, Fin (K j)) ℝ).repr_apply_apply u i).symm
  simp [projectionMass, hi, coordinateSet, weight]

theorem continuous_weight (K : Fin J → ℕ) (j : Fin J) :
    Continuous (fun u : BlockSpace K => weight K u j) := by
  have heq : (fun u : BlockSpace K => weight K u j) =
      projectionMass (EuclideanSpace.basisFun (Σ j, Fin (K j)) ℝ) (coordinateSet K j) := by
    funext u
    exact weight_eq_projectionMass K j u
  rw [heq]
  exact continuous_projectionMass _ _

theorem measurable_bad_weights (K : Fin J → ℕ) (ν : Fin J → ℝ) (δ : ℝ) :
    MeasurableSet {u : BlockSpace K | ∃ j, δ * ν j < |weight K u j - ν j|} := by
  simp only [Set.setOf_exists]
  apply MeasurableSet.iUnion
  intro j
  exact (isOpen_lt continuous_const ((continuous_weight K j).sub continuous_const).abs).measurableSet

theorem weight_relative_tail (K : Fin J → ℕ) (j : Fin J) (hK : 0 < K j)
    (η : ℝ) (hη : 0 < η) :
    sphereLaw (BlockSpace K) {u | η * ((K j : ℝ) / (∑ i, K i : ℕ)) ≤
      |weight K u j - (K j : ℝ) / (∑ i, K i : ℕ)|} ≤
      ENNReal.ofReal (2 / (η ^ 2 * (K j : ℝ))) := by
  haveI : Nonempty (Σ j, Fin (K j)) := ⟨⟨j, ⟨0, hK⟩⟩⟩
  have hset : (coordinateSet K j).Nonempty := Finset.card_pos.mp (by simpa using hK)
  have h := projectionMass_relative_tail (EuclideanSpace.basisFun (Σ j, Fin (K j)) ℝ)
    (coordinateSet K j) hset η hη
  simpa only [coordinateSet_card, Fintype.card_sigma, Fintype.card_fin,
    ← weight_eq_projectionMass] using h

theorem all_weights_relative_tail (K : Fin J → ℕ) (hK : ∀ j, 0 < K j)
    (η : ℝ) (hη : 0 < η) :
    sphereLaw (BlockSpace K) {u | ∃ j, η * ((K j : ℝ) / (∑ i, K i : ℕ)) ≤
      |weight K u j - (K j : ℝ) / (∑ i, K i : ℕ)|} ≤
      ∑ j, ENNReal.ofReal (2 / (η ^ 2 * (K j : ℝ))) := by
  calc
    _ = sphereLaw (BlockSpace K) (⋃ j, {u | η * ((K j : ℝ) / (∑ i, K i : ℕ)) ≤
        |weight K u j - (K j : ℝ) / (∑ i, K i : ℕ)|}) := by congr 1; ext u; simp
    _ ≤ ∑ j, sphereLaw (BlockSpace K) {u | η * ((K j : ℝ) / (∑ i, K i : ℕ)) ≤
        |weight K u j - (K j : ℝ) / (∑ i, K i : ℕ)|} := measure_iUnion_fintype_le _ _
    _ ≤ _ := Finset.sum_le_sum (fun j _ => weight_relative_tail K j (hK j) η hη)

/-- Combines multiplicity approximation with concentration around the
multiplicity ratios. -/
theorem relative_weight_transfer (ν κ ω δ : ℝ) (hν : 0 ≤ ν)
    (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hκ : |κ - ν| ≤ (δ / 4) * ν) (hω : |ω - κ| ≤ (δ / 4) * κ) :
    |ω - ν| ≤ δ * ν := by
  have ht : |ω - ν| ≤ |ω - κ| + |κ - ν| := by
    calc
      _ = |(ω - κ) + (κ - ν)| := by congr 1; ring
      _ ≤ _ := abs_add _ _
  have hκupper : κ ≤ ν + (δ / 4) * ν := by linarith [(abs_le.mp hκ).2]
  have hmul := mul_le_mul_of_nonneg_left hκupper (by positivity : 0 ≤ δ / 4)
  have hsq : δ ^ 2 ≤ δ := by nlinarith
  have hs := mul_le_mul_of_nonneg_right hsq hν
  nlinarith

theorem design_weights_bad_le (K : Fin J → ℕ) (hK : ∀ j, 0 < K j)
    (ν : Fin J → ℝ) (hν : ∀ j, 0 ≤ ν j) (δ : ℝ) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (happrox : ∀ j, |(K j : ℝ) / (∑ i, K i : ℕ) - ν j| ≤ (δ / 4) * ν j) :
    sphereLaw (BlockSpace K) {u | ∃ j, δ * ν j < |weight K u j - ν j|} ≤
      ∑ j, ENNReal.ofReal (2 / ((δ / 4) ^ 2 * (K j : ℝ))) := by
  apply le_trans (measure_mono ?_) (all_weights_relative_tail K hK (δ / 4) (by positivity))
  intro u hu
  obtain ⟨j, hj⟩ := hu
  refine ⟨j, ?_⟩
  by_contra! hsmall
  exact (not_lt_of_ge (relative_weight_transfer (ν j) ((K j : ℝ) / (∑ i, K i : ℕ))
    (weight K u j) δ (hν j) hδ hδone (happrox j) hsmall.le)) hj

end RandomizedFO2003.Spherical
