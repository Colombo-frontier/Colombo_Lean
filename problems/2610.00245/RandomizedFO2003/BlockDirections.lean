import RandomizedFO2003.InvariantProjection
import RandomizedFO2003.SpectralProjectors

namespace RandomizedFO2003.SpectralCoordinates

open MeasureTheory Spherical
open scoped BigOperators

variable {J : ℕ}

abbrev ComponentSpace (K : Fin J → ℕ) (j : Fin J) := EuclideanSpace ℝ (Fin (K j))

noncomputable def splitBlocks (K : Fin J → ℕ) :
    BlockSpace K ≃ₗᵢ[ℝ] PiLp 2 (ComponentSpace K) :=
  LinearIsometryEquiv.piLpCurry ℝ 2 (fun j (_ : Fin (K j)) => ℝ)

noncomputable def slice (K : Fin J → ℕ) (j : Fin J) (x : BlockSpace K) : ComponentSpace K j :=
  splitBlocks K x j

@[simp] theorem slice_apply (K : Fin J → ℕ) (j : Fin J) (x : BlockSpace K) (k : Fin (K j)) :
    slice K j x k = x ⟨j, k⟩ := rfl

theorem continuous_slice (K : Fin J → ℕ) (j : Fin J) : Continuous (slice K j) :=
  (PiLp.proj (𝕜 := ℝ) 2 (ComponentSpace K) j).continuous.comp (splitBlocks K).continuous

theorem slice_energy (K : Fin J → ℕ) (j : Fin J) (x : BlockSpace K) :
    ‖slice K j x‖ ^ 2 = weight K x j := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [PiLp.inner_apply, weight]
  apply Finset.sum_congr rfl
  intro k _
  change x ⟨j, k⟩ * x ⟨j, k⟩ = x ⟨j, k⟩ ^ 2
  ring

/-- Rotate just one eigenspace, leaving every other eigenspace unchanged. -/
noncomputable def rotateBlock (K : Fin J → ℕ) (j : Fin J)
    (U : ComponentSpace K j ≃ₗᵢ[ℝ] ComponentSpace K j) : BlockSpace K ≃ₗᵢ[ℝ] BlockSpace K :=
  (splitBlocks K).trans ((LinearIsometryEquiv.piLpCongrRight 2
    (Function.update (fun i => LinearIsometryEquiv.refl ℝ (ComponentSpace K i)) j U)).trans
      (splitBlocks K).symm)

theorem slice_rotateBlock (K : Fin J → ℕ) (j : Fin J)
    (U : ComponentSpace K j ≃ₗᵢ[ℝ] ComponentSpace K j) (x : BlockSpace K) :
    slice K j (rotateBlock K j U x) = U (slice K j x) := by
  simp [slice, rotateBlock, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.piLpCongrRight_apply]

theorem slice_rotateBlock_other (K : Fin J → ℕ) (j i : Fin J) (hij : i ≠ j)
    (U : ComponentSpace K j ≃ₗᵢ[ℝ] ComponentSpace K j) (x : BlockSpace K) :
    slice K i (rotateBlock K j U x) = slice K i x := by
  simp [slice, rotateBlock, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.piLpCongrRight_apply, hij]

theorem weight_rotateBlock (K : Fin J → ℕ) (j i : Fin J)
    (U : ComponentSpace K j ≃ₗᵢ[ℝ] ComponentSpace K j) (x : BlockSpace K) :
    weight K (rotateBlock K j U x) i = weight K x i := by
  rw [← slice_energy, ← slice_energy]
  by_cases hij : i = j
  · subst i
    rw [slice_rotateBlock, U.norm_map]
  · rw [slice_rotateBlock_other K j i hij]

noncomputable def blockDirection (K : Fin J → ℕ) (j : Fin J) (x : BlockSpace K) :
    ComponentSpace K j := radial (ComponentSpace K j) (slice K j x)

theorem measurable_blockDirection (K : Fin J → ℕ) (j : Fin J) :
    Measurable (blockDirection K j) :=
  (measurable_radial (ComponentSpace K j)).comp (continuous_slice K j).measurable

theorem blockDirection_norm_le (K : Fin J → ℕ) (j : Fin J) (x : BlockSpace K) :
    ‖blockDirection K j x‖ ≤ 1 := by
  by_cases hx : slice K j x = 0
  · simp [blockDirection, hx, radial]
  · exact (radial_norm (ComponentSpace K j) hx).le

theorem blockDirection_norm (K : Fin J → ℕ) (j : Fin J) (x : BlockSpace K)
    (hw : 0 < weight K x j) : ‖blockDirection K j x‖ = 1 := by
  apply radial_norm
  intro hx
  have hs := slice_energy K j x
  simp [hx] at hs
  linarith

theorem blockDirection_rotateBlock (K : Fin J → ℕ) (j : Fin J)
    (U : ComponentSpace K j ≃ₗᵢ[ℝ] ComponentSpace K j) (x : BlockSpace K) :
    blockDirection K j (rotateBlock K j U x) = U (blockDirection K j x) := by
  unfold blockDirection
  rw [slice_rotateBlock, radial_commutes]

noncomputable def blockDirectionLaw (K : Fin J → ℕ) (j : Fin J) : Measure (ComponentSpace K j) :=
  (sphereLaw (BlockSpace K)).map (blockDirection K j)

instance blockDirectionLaw_probability (K : Fin J → ℕ) (j : Fin J) :
    IsProbabilityMeasure (blockDirectionLaw K j) :=
  isProbabilityMeasure_map (measurable_blockDirection K j).aemeasurable

theorem blockDirectionLaw_ball (K : Fin J → ℕ) (j : Fin J) :
    ∀ᵐ x ∂blockDirectionLaw K j, ‖x‖ ≤ 1 := by
  apply (ae_map_iff (measurable_blockDirection K j).aemeasurable
    (isClosed_le continuous_norm continuous_const).measurableSet).mpr
  exact Filter.Eventually.of_forall (blockDirection_norm_le K j)

/-- The normalized component has an invariant law. The proof uses actual
block rotations and retains every spectral weight. -/
theorem blockDirectionLaw_invariant (K : Fin J → ℕ) (j : Fin J) :
    RotationInvariant (blockDirectionLaw K j) := by
  intro U
  refine ⟨U.continuous.measurable, ?_⟩
  unfold blockDirectionLaw
  rw [Measure.map_map U.continuous.measurable (measurable_blockDirection K j)]
  have hc : U ∘ blockDirection K j = blockDirection K j ∘ rotateBlock K j U := by
    funext x
    exact (blockDirection_rotateBlock K j U x).symm
  rw [hc, ← Measure.map_map (measurable_blockDirection K j) (rotateBlock K j U).continuous.measurable,
    (sphereLaw_invariant (BlockSpace K) (rotateBlock K j U)).map_eq]

theorem blockDirection_projection_tail (K : Fin J → ℕ) (j : Fin J) (hK : 0 < K j)
    (W : Submodule ℝ (ComponentSpace K j)) (η : ℝ) (hη : 0 < η) :
    sphereLaw (BlockSpace K) {u | η ≤ ‖W.orthogonalProjection (blockDirection K j u)‖} ≤
      ENNReal.ofReal ((Module.finrank ℝ W : ℝ) / ((K j : ℝ) * η ^ 2)) := by
  haveI : NeZero (K j) := ⟨Nat.ne_of_gt hK⟩
  have ht := invariant_projection_tail (blockDirectionLaw K j) (blockDirectionLaw_ball K j)
    (blockDirectionLaw_invariant K j) W η hη
  have hset : MeasurableSet {x : ComponentSpace K j | η ≤ ‖W.orthogonalProjection x‖} :=
    (isClosed_le continuous_const W.orthogonalProjection.continuous.norm).measurableSet
  rw [blockDirectionLaw, Measure.map_apply (measurable_blockDirection K j) hset] at ht
  simpa using ht

end RandomizedFO2003.SpectralCoordinates
