import Mathlib

/-!
Concrete normalized Haar probability on the real orthogonal group, measurable
orthonormal columns, and their rotationally invariant unit-sphere laws.
Only generic compact-group/linear-algebra infrastructure is used. No
concentration assertion is introduced as an axiom or a typeclass premise.
-/

open Set MeasureTheory MeasureTheory.Measure ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace Matrix

namespace Task006.HaarRebalancing

noncomputable section

/-- The orthogonal group in dimension `d`, with its induced Borel structure. -/
abbrev OrthogonalGroup (d : ℕ) := Matrix.orthogonalGroup (Fin d) ℝ

/-- Matrices do not carry a global measurable-space instance in mathlib,
because several matrix norms are available.  The canonical product topology is
unambiguous, so we explicitly choose its Borel sigma algebra here. -/
noncomputable instance realMatrixMeasurableSpace (d : ℕ) :
    MeasurableSpace (Matrix (Fin d) (Fin d) ℝ) := borel _

instance realMatrixBorelSpace (d : ℕ) :
    BorelSpace (Matrix (Fin d) (Fin d) ℝ) := ⟨rfl⟩

section CompactHaar

variable (d : ℕ)

theorem orthogonalGroup_isCompact :
    IsCompact (unitary (Matrix (Fin d) (Fin d) ℝ) :
      Set (Matrix (Fin d) (Fin d) ℝ)) := by
  apply isCompact_Icc.matrix.of_isClosed_subset isClosed_unitary
  intro Q hQ
  rw [Set.mem_matrix]
  intro i j
  have habs : |Q i j| ≤ 1 := by
    simpa [Real.norm_eq_abs] using entry_norm_bound_of_unitary hQ i j
  exact abs_le.mp habs

noncomputable instance orthogonalGroupCompactSpace : CompactSpace (OrthogonalGroup d) :=
  isCompact_iff_compactSpace.mp (orthogonalGroup_isCompact d)

/-- Normalized Haar probability on `O(d)`. -/
def orthogonalHaarCompact :
    TopologicalSpace.PositiveCompacts (OrthogonalGroup d) :=
  ⟨⟨Set.univ, CompactSpace.isCompact_univ⟩, by simp⟩

/-- Normalized Haar probability on `O(d)`. -/
def orthogonalHaarProbability : Measure (OrthogonalGroup d) :=
  haarMeasure (orthogonalHaarCompact d)

instance orthogonalHaarProbability_isProbability :
    IsProbabilityMeasure (orthogonalHaarProbability d) where
  measure_univ := by
    simpa [orthogonalHaarProbability, orthogonalHaarCompact] using
      (haarMeasure_self (K₀ := orthogonalHaarCompact d))

instance orthogonalHaarProbability_isHaar :
    Measure.IsHaarMeasure (orthogonalHaarProbability d) := by
  change Measure.IsHaarMeasure (haarMeasure (orthogonalHaarCompact d))
  infer_instance

end CompactHaar

section Columns

variable {d : ℕ}

/-- Column `j` of an orthogonal matrix, as a vector in Euclidean space. -/
def column (Q : OrthogonalGroup d) (j : Fin d) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => Q i j)

theorem measurable_column (j : Fin d) :
    Measurable (fun Q : OrthogonalGroup d => column Q j) := by
  apply (WithLp.measurable_toLp 2 (Fin d → ℝ)).comp
  refine measurable_pi_lambda _ fun i => ?_
  have hcoord : Continuous
      (fun Q : OrthogonalGroup d => (Q : Matrix (Fin d) (Fin d) ℝ) i j) := by
    have hm : Continuous
        (fun Q : Matrix (Fin d) (Fin d) ℝ => Q i j) :=
      (continuous_apply j).comp (continuous_apply i)
    exact hm.comp continuous_subtype_val
  exact hcoord.measurable

theorem orthonormal_column (Q : OrthogonalGroup d) :
    Orthonormal ℝ (column Q) := by
  rw [orthonormal_iff_ite]
  intro i j
  have hQ : star (Q : Matrix (Fin d) (Fin d) ℝ) * Q = 1 := Q.property.1
  simpa [column, Matrix.mul_apply, PiLp.inner_apply, Matrix.one_apply,
    mul_comm, eq_comm] using
    congrFun (congrFun hQ j) i


end Columns

variable {d : ℕ}

/-- The orthogonal matrix of a Euclidean linear isometry, in the canonical basis. -/
def orthogonalMatrixOfLinearIsometryEquiv
    (U : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) :
    OrthogonalGroup d :=
  ⟨U.toMatrix (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin d) ℝ).toBasis,
    U.toMatrix_mem_unitaryGroup (EuclideanSpace.basisFun (Fin d) ℝ)
      (EuclideanSpace.basisFun (Fin d) ℝ)⟩

/-- Left multiplication by the matrix of `U` applies `U` to every column. -/
theorem column_mul_orthogonalMatrixOfLinearIsometryEquiv
    (U : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (Q : OrthogonalGroup d) (j : Fin d) :
    column (orthogonalMatrixOfLinearIsometryEquiv U * Q) j =
      U (column Q j) := by
  apply WithLp.ofLp_injective 2
  change (fun i => ((orthogonalMatrixOfLinearIsometryEquiv U :
      Matrix (Fin d) (Fin d) ℝ) * (Q : Matrix (Fin d) (Fin d) ℝ)) i j) =
    (U (column Q j)).ofLp
  have h := LinearMap.toMatrix_mulVec_repr
    (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin d) ℝ).toBasis U.toLinearMap
    (column Q j)
  have hrepr : (EuclideanSpace.basisFun (Fin d) ℝ).toBasis.repr
      (column Q j) = fun i => (Q : Matrix (Fin d) (Fin d) ℝ) i j := by
    funext q
    simp [column, OrthonormalBasis.coe_toBasis_repr_apply]
  rw [hrepr] at h
  funext i
  have hi := congrFun h i
  simpa [orthogonalMatrixOfLinearIsometryEquiv, column,
    OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
    Matrix.mul_apply, Matrix.mulVec, dotProduct] using hi


/-- A concrete vector law is uniform on the unit sphere when it is supported
on unit vectors and invariant under every real linear isometry. -/
structure UniformSphereLaw {Ω : Type*} [MeasurableSpace Ω]
    (v : Ω → EuclideanSpace ℝ (Fin d)) (μ : Measure Ω) : Prop where
  measurable : AEMeasurable v μ
  unit_ae : ∀ᵐ ω ∂μ, ‖v ω‖ = 1
  rotationInvariant : ∀ U : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d),
    Measure.map (fun ω => U (v ω)) μ = Measure.map v μ

/-- Every fixed column of a genuinely Haar-distributed orthogonal matrix has
a rotationally invariant probability law supported on the unit sphere. -/
theorem column_isUniform (j : Fin d) :
    UniformSphereLaw (fun Q : OrthogonalGroup d => column Q j)
      (orthogonalHaarProbability d) := by
  refine ⟨(measurable_column j).aemeasurable, ?_, ?_⟩
  · filter_upwards [] with Q
    exact (orthonormal_column Q).norm_eq_one j
  · intro U
    let A : OrthogonalGroup d := orthogonalMatrixOfLinearIsometryEquiv U
    have hpoint : (fun Q : OrthogonalGroup d => U (column Q j)) =
        fun Q => column (A * Q) j := by
      funext Q
      exact (column_mul_orthogonalMatrixOfLinearIsometryEquiv U Q j).symm
    rw [hpoint]
    calc
      Measure.map (fun Q : OrthogonalGroup d => column (A * Q) j)
          (orthogonalHaarProbability d) =
          Measure.map (column · j)
            (Measure.map (fun Q : OrthogonalGroup d => A * Q)
              (orthogonalHaarProbability d)) := by
                symm
                rw [Measure.map_map (measurable_column j) (measurable_const_mul A)]
                rfl
      _ = Measure.map (column · j) (orthogonalHaarProbability d) := by
        rw [map_mul_left_eq_self]


end
end Task006.HaarRebalancing
