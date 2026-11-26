import MatchingBounds1005.GaussianBlockGeometry
import RandomizedFO2003.MultiStart

/-! # A concrete spectral-coordinate model for high-multiplicity Gaussian geometry

The spectral identities required by the block theorem are proved for an
actual repeated diagonal operator; they are not supplied as assumptions.
-/

noncomputable section
open MeasureTheory
open scoped InnerProductSpace BigOperators
open RandomizedFO2003.SpectralCoordinates
open MatchingBounds1005.GaussianVector MatchingBounds1005.GaussianMatrix
open MatchingBounds1005.GaussianBlockGeometry

namespace MatchingBounds1005.SpectralGaussian

def componentInsert {J : ℕ} (dim : Fin J → ℕ) (j : Fin J) :
    Vec (dim j) →ₗᵢ[ℝ] PiLp 2 (ComponentSpace dim) where
  toFun x := (WithLp.equiv 2 (∀ j, ComponentSpace dim j)).symm (Pi.single j x)
  map_add' x y := by ext i; simp [Pi.single_add]
  map_smul' c x := by ext i; simp [Pi.single_smul]
  norm_map' x := PiLp.norm_equiv_symm_single 2 (ComponentSpace dim) j x

theorem componentInsert_inner {J : ℕ} (dim : Fin J → ℕ) (j : Fin J)
    (v : Vec (dim j)) (x : PiLp 2 (ComponentSpace dim)) :
    ⟪componentInsert dim j v, x⟫_ℝ = ⟪v, x j⟫_ℝ := by
  change (∑ i, ⟪Pi.single j v i, x i⟫_ℝ) = _
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · simp

abbrev ambientDimension {J : ℕ} (dim : Fin J → ℕ) := Module.finrank ℝ (BlockSpace dim)

def ambientIso {J : ℕ} (dim : Fin J → ℕ) : Vec (ambientDimension dim) ≃ₗᵢ[ℝ] BlockSpace dim :=
  (stdOrthonormalBasis ℝ (BlockSpace dim)).repr.symm

def spectralEmbedding {J : ℕ} (dim : Fin J → ℕ) (j : Fin J) :
    Vec (dim j) →ₗᵢ[ℝ] Vec (ambientDimension dim) :=
  (ambientIso dim).symm.toLinearIsometry.comp
    ((splitBlocks dim).symm.toLinearIsometry.comp (componentInsert dim j))

theorem spectralEmbedding_apply {J : ℕ} (dim : Fin J → ℕ) (j : Fin J) (v : Vec (dim j)) :
    ambientIso dim (spectralEmbedding dim j v) = (splitBlocks dim).symm (componentInsert dim j v) := by
  simp [spectralEmbedding]

theorem blockCoordinates_eq_slice {J : ℕ} (dim : Fin J → ℕ) (j : Fin J)
    (x : Vec (ambientDimension dim)) :
    blockCoordinates (spectralEmbedding dim) j x = slice dim j (ambientIso dim x) := by
  apply ext_inner_left ℝ
  intro v
  change ⟪v, (spectralEmbedding dim j).toContinuousLinearMap.adjoint x⟫_ℝ = _
  rw [ContinuousLinearMap.adjoint_inner_right]
  change ⟪spectralEmbedding dim j v, x⟫_ℝ = _
  rw [← (ambientIso dim).inner_map_map, spectralEmbedding_apply,
    ← (splitBlocks dim).inner_map_map]
  simp only [LinearIsometryEquiv.apply_symm_apply]
  exact componentInsert_inner dim j v _

theorem spectral_inner_decomposition {J : ℕ} (dim : Fin J → ℕ)
    (x y : Vec (ambientDimension dim)) :
    ⟪x, y⟫_ℝ = ∑ j, ⟪blockCoordinates (spectralEmbedding dim) j x,
      blockCoordinates (spectralEmbedding dim) j y⟫_ℝ := by
  simp_rw [blockCoordinates_eq_slice]
  rw [← (ambientIso dim).inner_map_map]
  exact inner_eq_sum_slices dim _ _

def spectralOperator {J : ℕ} (dim : Fin J → ℕ) (node : Fin J → ℝ) :
    Vec (ambientDimension dim) →L[ℝ] Vec (ambientDimension dim) :=
  (ambientIso dim).symm.toContinuousLinearMap.comp
    ((LinearMap.toContinuousLinearMap (diagonal dim node)).comp (ambientIso dim).toContinuousLinearMap)

theorem spectralOperator_coordinates {J : ℕ} (dim : Fin J → ℕ) (node : Fin J → ℝ)
    (j : Fin J) (x : Vec (ambientDimension dim)) :
    blockCoordinates (spectralEmbedding dim) j (spectralOperator dim node x) =
      node j • blockCoordinates (spectralEmbedding dim) j x := by
  rw [blockCoordinates_eq_slice, blockCoordinates_eq_slice]
  change slice dim j (ambientIso dim ((ambientIso dim).symm (diagonal dim node (ambientIso dim x)))) = _
  rw [LinearIsometryEquiv.apply_symm_apply, slice_diagonal]

/-- The actual repeated spectral operator satisfies the whole-cyclic-span
probability bound, with the structural decomposition discharged. -/
theorem spectral_high_multiplicity {J k K : ℕ} (dim : Fin J → ℕ) (node : Fin J → ℝ)
    (A : (j : Fin J) → Submodule ℝ (Vec (dim j)))
    (hm : ∀ j, 0 < Module.finrank ℝ (A j))
    (hd : ∀ j, dim j = (K + 1) * Module.finrank ℝ (A j))
    {η s : ℝ} (hη : 0 ≤ η) (hηhalf : η ≤ 1 / 2) (hs : 0 ≤ s)
    (hK : 96 * ((k : ℝ) + 1) + 32 * s ≤ ((K + 1 : ℕ) : ℝ) * η ^ 2) :
    (gaussianMatrixLaw (ambientDimension dim) k).real
      {g | ¬ CyclicAngleGood (blockSubspace (spectralEmbedding dim) A) (spectralOperator dim node) g η} ≤
        4 * (J : ℝ) * Real.exp (-s) :=
  high_multiplicity_cyclic_angle (spectralEmbedding dim) (spectral_inner_decomposition dim)
    A hm hd (spectralOperator dim node) node (spectralOperator_coordinates dim node) hη hηhalf hs hK

/-- A measurable simultaneous good event with the requested confidence.
The universal constant differs from the manuscript, while the dependence
on starts, confidence and multiplicity has exactly the same exponents. -/
theorem spectral_high_probability {J k K : ℕ} (hJ : 0 < J)
    (dim : Fin J → ℕ) (node : Fin J → ℝ)
    (A : (j : Fin J) → Submodule ℝ (Vec (dim j)))
    (hm : ∀ j, 0 < Module.finrank ℝ (A j))
    (hd : ∀ j, dim j = (K + 1) * Module.finrank ℝ (A j))
    {η ζ : ℝ} (hη : 0 ≤ η) (hηhalf : η ≤ 1 / 2) (hζ : 0 < ζ) (hζone : ζ ≤ 1)
    (hK : 96 * ((k : ℝ) + 1) + 32 * Real.log (4 * (J : ℝ) / ζ) ≤
      ((K + 1 : ℕ) : ℝ) * η ^ 2) :
    ∃ G : Set (Fin k → Vec (ambientDimension dim)), MeasurableSet G ∧
      (∀ g ∈ G, CyclicAngleGood (blockSubspace (spectralEmbedding dim) A)
        (spectralOperator dim node) g η) ∧
      1 - ζ ≤ (gaussianMatrixLaw (ambientDimension dim) k).real G := by
  have hJ' : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have harg : 0 < 4 * (J : ℝ) / ζ := by positivity
  have hlog : 0 ≤ Real.log (4 * (J : ℝ) / ζ) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ hζ).2
    linarith
  have hh := spectral_high_multiplicity dim node A hm hd hη hηhalf hlog hK
  have he : 4 * (J : ℝ) * Real.exp (-Real.log (4 * (J : ℝ) / ζ)) = ζ := by
    rw [Real.exp_neg, Real.exp_log harg]
    field_simp
  rw [he] at hh
  exact measurable_good_event _ _ hh

/-- The same measurable good event is transported to the exact independent
Gaussian history used by the adaptive Haar simulation, including its seed. -/
theorem spectral_history_high_probability {J K : ℕ} (hJ : 0 < J)
    (dim : Fin J → ℕ) (node : Fin J → ℝ)
    (A : (j : Fin J) → Submodule ℝ (Vec (dim j)))
    (hm : ∀ j, 0 < Module.finrank ℝ (A j))
    (hd : ∀ j, dim j = (K + 1) * Module.finrank ℝ (A j))
    (steps : ℕ) {H : Type*} [MeasurableSpace H] (μ : Measure H) [IsProbabilityMeasure μ]
    {η ζ : ℝ} (hη : 0 ≤ η) (hηhalf : η ≤ 1 / 2) (hζ : 0 < ζ) (hζone : ζ ≤ 1)
    (hK : 96 * (((steps + steps : ℕ) : ℝ) + 1) + 32 * Real.log (4 * (J : ℝ) / ζ) ≤
      ((K + 1 : ℕ) : ℝ) * η ^ 2) :
    ∃ G : Set (RandomizedFO2003.Rotations.AmbientPairHistory (Vec (ambientDimension dim)) steps H),
      MeasurableSet G ∧
      (∀ p ∈ G, CyclicAngleGood (blockSubspace (spectralEmbedding dim) A)
        (spectralOperator dim node)
        (RandomizedFO2003.Rotations.AmbientPairHistory.starts (Vec (ambientDimension dim)) steps p) η) ∧
      1 - ζ ≤ (GaussianHaar.gaussianPairLaw (ambientDimension dim) steps μ).real G := by
  obtain ⟨G, hG, hgood, hprob⟩ := spectral_high_probability hJ dim node A hm hd
    hη hηhalf hζ hζone hK
  have hp := GaussianStarts.starts_preserving (ambientDimension dim) steps μ
  refine ⟨_ ⁻¹' G, hG.preimage hp.measurable, ?_, ?_⟩
  · intro p hmem
    exact hgood _ hmem
  · rw [hp.measureReal_preimage hG.nullMeasurableSet]
    exact hprob

end MatchingBounds1005.SpectralGaussian
