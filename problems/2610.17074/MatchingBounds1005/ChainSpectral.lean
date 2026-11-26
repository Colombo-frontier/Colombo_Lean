import MatchingBounds1005.ChainCopies
import MatchingBounds1005.GaussianBlockGeometry

/-! # Gaussian geometry for the actual chain and its decoy copies

The spectral coordinates are constructed from the actual chain operator's
orthonormal eigenbasis. Repeated eigenvalues need not be merged: each base
eigenvector contributes one block of `K+1` identical copies and one active
coordinate. Thus the union bound has at most the base dimension many blocks.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace
open MatchingBounds1005.GaussianVector MatchingBounds1005.GaussianMatrix
open MatchingBounds1005.GaussianBlockGeometry

namespace MatchingBounds1005.BlockGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

abbrev baseDimension (n : ℕ) := Module.finrank ℝ (BlockSpace (E := E) n)
abbrev copyDimension (n K : ℕ) := Module.finrank ℝ (CopySpace (E := E) n K)

theorem copyDimension_eq (n K : ℕ) :
    copyDimension (E := E) n K = (K + 1) * baseDimension (E := E) n := by
  change Module.finrank ℝ (PiLp 2 (fun _ : Fin (K + 1) => BlockSpace (E := E) n)) = _
  rw [(WithLp.linearEquiv 2 ℝ (Fin (K + 1) → BlockSpace (E := E) n)).finrank_eq]
  simp [Module.finrank_pi_fintype, baseDimension]

def chainEigenbasis (G : BlockGeometry E) (n : ℕ) :
    OrthonormalBasis (Fin (baseDimension (E := E) n)) ℝ (BlockSpace (E := E) n) :=
  (G.chainOperator_symmetric n).eigenvectorBasis rfl

def chainEigenvalue (G : BlockGeometry E) (n : ℕ) : Fin (baseDimension (E := E) n) → ℝ :=
  (G.chainOperator_symmetric n).eigenvalues rfl

theorem chainEigenbasis_operator (G : BlockGeometry E) (n : ℕ)
    (z : BlockSpace (E := E) n) (i : Fin (baseDimension (E := E) n)) :
    (G.chainEigenbasis n).repr (G.chainOperator n z) i =
      G.chainEigenvalue n i * (G.chainEigenbasis n).repr z i :=
  (G.chainOperator_symmetric n).eigenvectorBasis_apply_self_apply rfl z i

def copyEuclideanIso (n K : ℕ) : Vec (copyDimension (E := E) n K) ≃ₗᵢ[ℝ] CopySpace (E := E) n K :=
  (stdOrthonormalBasis ℝ (CopySpace (E := E) n K)).repr.symm

def copyEigenInsert (G : BlockGeometry E) (n K : ℕ) (i : Fin (baseDimension (E := E) n)) :
    Vec (K + 1) →ₗᵢ[ℝ] CopySpace (E := E) n K where
  toFun v := (WithLp.equiv 2 (Fin (K + 1) → BlockSpace (E := E) n)).symm
    (fun j => v j • G.chainEigenbasis n i)
  map_add' v w := by ext j : 1; simp [add_smul]
  map_smul' c v := by ext j : 1; simp [smul_smul]
  norm_map' v := by
    change ‖(WithLp.equiv 2 (Fin (K + 1) → BlockSpace (E := E) n)).symm
      (fun j => v j • G.chainEigenbasis n i)‖ = ‖v‖
    have hs : ‖(WithLp.equiv 2 (Fin (K + 1) → BlockSpace (E := E) n)).symm
        (fun j => v j • G.chainEigenbasis n i)‖ ^ 2 = ‖v‖ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
      apply Finset.sum_congr rfl
      intro j _
      simp only [WithLp.equiv_symm_pi_apply, norm_smul, (G.chainEigenbasis n).norm_eq_one, mul_one]
    nlinarith [norm_nonneg v, norm_nonneg ((WithLp.equiv 2 (Fin (K + 1) → BlockSpace (E := E) n)).symm
      (fun j => v j • G.chainEigenbasis n i))]

def copyEigenSlice (G : BlockGeometry E) (n K : ℕ) (i : Fin (baseDimension (E := E) n))
    (z : CopySpace (E := E) n K) : Vec (K + 1) :=
  (WithLp.equiv 2 _).symm (fun j => (G.chainEigenbasis n).repr (z j) i)

theorem copyEigenInsert_inner (G : BlockGeometry E) (n K : ℕ)
    (i : Fin (baseDimension (E := E) n)) (v : Vec (K + 1)) (z : CopySpace (E := E) n K) :
    ⟪G.copyEigenInsert n K i v, z⟫_ℝ = ⟪v, G.copyEigenSlice n K i z⟫_ℝ := by
  change (∑ j, ⟪v j • G.chainEigenbasis n i, z j⟫_ℝ) =
    ∑ j, (G.chainEigenbasis n).repr (z j) i * v j
  apply Finset.sum_congr rfl
  intro j _
  rw [real_inner_smul_left, OrthonormalBasis.repr_apply_apply, mul_comm]

def copySpectralEmbedding (G : BlockGeometry E) (n K : ℕ)
    (i : Fin (baseDimension (E := E) n)) : Vec (K + 1) →ₗᵢ[ℝ] Vec (copyDimension (E := E) n K) :=
  (copyEuclideanIso n K).symm.toLinearIsometry.comp (G.copyEigenInsert n K i)

theorem copy_blockCoordinates (G : BlockGeometry E) (n K : ℕ)
    (i : Fin (baseDimension (E := E) n)) (x : Vec (copyDimension (E := E) n K)) :
    blockCoordinates (G.copySpectralEmbedding n K) i x =
      G.copyEigenSlice n K i (copyEuclideanIso n K x) := by
  apply ext_inner_left ℝ
  intro v
  change ⟪v, (G.copySpectralEmbedding n K i).toContinuousLinearMap.adjoint x⟫_ℝ = _
  rw [ContinuousLinearMap.adjoint_inner_right]
  change ⟪G.copySpectralEmbedding n K i v, x⟫_ℝ = _
  rw [← (copyEuclideanIso (E := E) n K).inner_map_map]
  change ⟪copyEuclideanIso n K ((copyEuclideanIso n K).symm (G.copyEigenInsert n K i v)),
    copyEuclideanIso n K x⟫_ℝ = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact G.copyEigenInsert_inner n K i v _

theorem copy_inner_decomposition (G : BlockGeometry E) (n K : ℕ)
    (x y : Vec (copyDimension (E := E) n K)) :
    ⟪x, y⟫_ℝ = ∑ i, ⟪blockCoordinates (G.copySpectralEmbedding n K) i x,
      blockCoordinates (G.copySpectralEmbedding n K) i y⟫_ℝ := by
  simp_rw [G.copy_blockCoordinates]
  rw [← (copyEuclideanIso (E := E) n K).inner_map_map]
  change (∑ j, ⟪copyEuclideanIso n K x j, copyEuclideanIso n K y j⟫_ℝ) =
    ∑ i, ∑ j, (G.chainEigenbasis n).repr (copyEuclideanIso n K y j) i *
      (G.chainEigenbasis n).repr (copyEuclideanIso n K x j) i
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← (G.chainEigenbasis n).repr.inner_map_map]
  rfl

def copyAmbientOperator (G : BlockGeometry E) (n K : ℕ) :
    Vec (copyDimension (E := E) n K) →L[ℝ] Vec (copyDimension (E := E) n K) :=
  (copyEuclideanIso n K).symm.toContinuousLinearMap.comp
    ((G.copyOperator n K).comp (copyEuclideanIso n K).toContinuousLinearMap)

theorem copyAmbientOperator_coordinates (G : BlockGeometry E) (n K : ℕ)
    (i : Fin (baseDimension (E := E) n)) (x : Vec (copyDimension (E := E) n K)) :
    blockCoordinates (G.copySpectralEmbedding n K) i (G.copyAmbientOperator n K x) =
      G.chainEigenvalue n i • blockCoordinates (G.copySpectralEmbedding n K) i x := by
  rw [G.copy_blockCoordinates, G.copy_blockCoordinates]
  change G.copyEigenSlice n K i (copyEuclideanIso n K ((copyEuclideanIso n K).symm
    (G.copyOperator n K (copyEuclideanIso n K x)))) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  ext j
  exact G.chainEigenbasis_operator n _ i

def activeCoordinate (K : ℕ) : Vec (K + 1) := EuclideanSpace.single 0 1

def activeCoordinateSpace (K : ℕ) : Submodule ℝ (Vec (K + 1)) := ℝ ∙ activeCoordinate K

theorem activeCoordinateSpace_finrank (K : ℕ) : Module.finrank ℝ (activeCoordinateSpace K) = 1 := by
  apply finrank_span_singleton
  intro h
  have hh := congrArg (fun v : Vec (K + 1) => v 0) h
  simp [activeCoordinate, EuclideanSpace.single_apply] at hh

def copyAmbientActiveSpace (n K : ℕ) : Submodule ℝ (Vec (copyDimension (E := E) n K)) :=
  (activeSpace (E := E) n K).map (copyEuclideanIso n K).symm.toLinearEquiv.toLinearMap

theorem copyActive_le_blockSubspace (G : BlockGeometry E) (n K : ℕ) :
    copyAmbientActiveSpace (E := E) n K ≤
      blockSubspace (G.copySpectralEmbedding n K) (fun _ => activeCoordinateSpace K) := by
  rintro x ⟨z, ⟨v, rfl⟩, rfl⟩ i
  rw [G.copy_blockCoordinates]
  change G.copyEigenSlice n K i (copyEuclideanIso n K
    ((copyEuclideanIso n K).symm (activeInsert n K v))) ∈ _
  rw [LinearIsometryEquiv.apply_symm_apply]
  have he : G.copyEigenSlice n K i (activeInsert n K v) =
      (G.chainEigenbasis n).repr v i • activeCoordinate K := by
    ext j
    by_cases hj : j = 0
    · subst j
      simp [copyEigenSlice, activeInsert, activeCoordinate, EuclideanSpace.single_apply]
    · simp [copyEigenSlice, activeInsert, activeCoordinate, EuclideanSpace.single_apply, Pi.single_apply, hj]
  rw [he]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))

/-- The high-multiplicity bound for the actual symmetric chain copied `K+1`
times. All spectral identities and active-coordinate dimensions are derived. -/
theorem chain_copy_high_multiplicity (G : BlockGeometry E) (n K k : ℕ)
    {η s : ℝ} (hη : 0 ≤ η) (hηhalf : η ≤ 1 / 2) (hs : 0 ≤ s)
    (hK : 96 * ((k : ℝ) + 1) + 32 * s ≤ ((K + 1 : ℕ) : ℝ) * η ^ 2) :
    (gaussianMatrixLaw (copyDimension (E := E) n K) k).real
      {g | ¬ CyclicAngleGood (copyAmbientActiveSpace n K) (G.copyAmbientOperator n K) g η} ≤
        4 * (baseDimension (E := E) n : ℝ) * Real.exp (-s) := by
  have hb := high_multiplicity_cyclic_angle (G.copySpectralEmbedding n K)
    (G.copy_inner_decomposition n K) (fun _ => activeCoordinateSpace K)
    (fun _ => by rw [activeCoordinateSpace_finrank]; omega)
    (fun _ => by rw [activeCoordinateSpace_finrank]; omega)
    (G.copyAmbientOperator n K) (G.chainEigenvalue n)
    (G.copyAmbientOperator_coordinates n K) hη hηhalf hs hK
  apply le_trans (measureReal_mono ?_) hb
  intro g hg hgood
  exact hg (fun x hx => hgood x (G.copyActive_le_blockSubspace n K hx))

end MatchingBounds1005.BlockGeometry
