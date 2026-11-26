import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Deterministic completion of partial orthogonal data

The finite-dimensional linear isometry prescribed on a subspace extends to the whole
space. All extensions are parameterized exactly by the isometries between the two
orthogonal complements. These results concern deterministic maps; no conditional
Haar law or disintegration is asserted here.
-/

noncomputable section

open scoped InnerProductSpace

namespace NCConcave16991.PartialIsometry

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  (D : Submodule ℝ E) (R : Submodule ℝ F)

/-- The full isometry agrees with all prescribed forward data on `D`. -/
def ExtendsPartial (U : D ≃ₗᵢ[ℝ] R) (Q : E ≃ₗᵢ[ℝ] F) : Prop :=
  ∀ x : D, Q (x : E) = (U x : F)

/-- Glue the prescribed isometry and any complement isometry by orthogonal decomposition. -/
def completion (U : D ≃ₗᵢ[ℝ] R) (V : Dᗮ ≃ₗᵢ[ℝ] Rᗮ) : E ≃ₗᵢ[ℝ] F :=
  D.orthogonalDecomposition.trans
    ((LinearIsometryEquiv.withLpProdCongr 2 U V).trans R.orthogonalDecomposition.symm)

/-- The completion has an explicit pointwise orthogonal-sum formula. -/
theorem completion_apply (U : D ≃ₗᵢ[ℝ] R) (V : Dᗮ ≃ₗᵢ[ℝ] Rᗮ) (x : E) :
    completion D R U V x =
      (U (D.orthogonalProjectionOnto x) : F) +
        (V (Dᗮ.orthogonalProjectionOnto x) : F) := by
  simp [completion]

@[simp]
theorem completion_on_domain (U : D ≃ₗᵢ[ℝ] R) (V : Dᗮ ≃ₗᵢ[ℝ] Rᗮ) (x : D) :
    completion D R U V (x : E) = (U x : F) := by
  rw [completion_apply]
  simp [D.orthogonalProjectionOnto_orthogonal_apply_eq_zero x.property]

@[simp]
theorem completion_on_complement (U : D ≃ₗᵢ[ℝ] R) (V : Dᗮ ≃ₗᵢ[ℝ] Rᗮ)
    (x : Dᗮ) : completion D R U V (x : E) = (V x : F) := by
  rw [completion_apply]
  simp [D.orthogonalProjectionOnto_apply_of_mem_orthogonal x.property]

 theorem completion_extends (U : D ≃ₗᵢ[ℝ] R) (V : Dᗮ ≃ₗᵢ[ℝ] Rᗮ) :
    ExtendsPartial D R U (completion D R U V) := completion_on_domain D R U V

/-- The prescribed inverse data are forced by the prescribed forward data. -/
theorem extension_symm (U : D ≃ₗᵢ[ℝ] R) (Q : E ≃ₗᵢ[ℝ] F)
    (hQ : ExtendsPartial D R U Q) : ExtendsPartial R D U.symm Q.symm := by
  intro y
  apply Q.injective
  rw [Q.apply_symm_apply, hQ]
  simp

/-- In real inner product spaces, the forced inverse data are precisely the transpose data. -/
theorem extension_transpose_data (U : D ≃ₗᵢ[ℝ] R) (Q : E ≃ₗᵢ[ℝ] F)
    (hQ : ExtendsPartial D R U Q) (x : E) (y : R) :
    ⟪Q x, (y : F)⟫_ℝ = ⟪x, (U.symm y : E)⟫_ℝ := by
  rw [Q.inner_map_eq_flip, extension_symm D R U Q hQ y]

/-- Every extension maps the orthogonal complement into the prescribed range complement. -/
theorem extension_mem_orthogonal (U : D ≃ₗᵢ[ℝ] R) (Q : E ≃ₗᵢ[ℝ] F)
    (hQ : ExtendsPartial D R U Q) (x : Dᗮ) : Q (x : E) ∈ Rᗮ := by
  rw [Submodule.mem_orthogonal]
  intro y hy
  let z : R := ⟨y, hy⟩
  have hz : Q (U.symm z : E) = y := by rw [hQ]; simp [z]
  rw [← hz, Q.inner_map_map]
  exact (D.mem_orthogonal (x : E)).mp x.property _ (U.symm z).property

/-- The complement parameter recovered from any full extension. -/
def complementRestriction (U : D ≃ₗᵢ[ℝ] R) (Q : E ≃ₗᵢ[ℝ] F)
    (hQ : ExtendsPartial D R U Q) : Dᗮ ≃ₗᵢ[ℝ] Rᗮ where
  toFun x := ⟨Q (x : E), extension_mem_orthogonal D R U Q hQ x⟩
  invFun y := ⟨Q.symm (y : F),
    extension_mem_orthogonal R D U.symm Q.symm (extension_symm D R U Q hQ) y⟩
  left_inv x := by apply Subtype.ext; exact Q.symm_apply_apply (x : E)
  right_inv y := by apply Subtype.ext; exact Q.apply_symm_apply (y : F)
  map_add' x y := by apply Subtype.ext; exact Q.map_add (x : E) (y : E)
  map_smul' c x := by apply Subtype.ext; exact Q.map_smul c (x : E)
  norm_map' x := Q.norm_map (x : E)

@[simp]
theorem complementRestriction_apply (U : D ≃ₗᵢ[ℝ] R) (Q : E ≃ₗᵢ[ℝ] F)
    (hQ : ExtendsPartial D R U Q) (x : Dᗮ) :
    (complementRestriction D R U Q hQ x : F) = Q (x : E) := rfl

/-- Recovering the complement and gluing recovers the full extension pointwise. -/
theorem completion_complementRestriction_apply (U : D ≃ₗᵢ[ℝ] R)
    (Q : E ≃ₗᵢ[ℝ] F) (hQ : ExtendsPartial D R U Q) (x : E) :
    completion D R U (complementRestriction D R U Q hQ) x = Q x := by
  rw [completion_apply, complementRestriction_apply, ← hQ, ← Q.map_add]
  congr 1
  simpa using D.orthogonalDecomposition.symm_apply_apply x

/-- Complement isometries parameterize all completions, with no redundant parameters. -/
def completionEquiv (U : D ≃ₗᵢ[ℝ] R) :
    (Dᗮ ≃ₗᵢ[ℝ] Rᗮ) ≃ {Q : E ≃ₗᵢ[ℝ] F // ExtendsPartial D R U Q} where
  toFun V := ⟨completion D R U V, completion_extends D R U V⟩
  invFun Q := complementRestriction D R U Q.val Q.property
  left_inv V := by
    apply LinearIsometryEquiv.ext
    intro x
    apply Subtype.ext
    exact completion_on_complement D R U V x
  right_inv Q := by
    apply Subtype.ext
    apply LinearIsometryEquiv.ext
    exact completion_complementRestriction_apply D R U Q.val Q.property

/-- Equal ambient dimensions and isometric prescribed subspaces force equal complement dimensions. -/
theorem complement_finrank_eq (U : D ≃ₗᵢ[ℝ] R)
    (hEF : Module.finrank ℝ E = Module.finrank ℝ F) :
    Module.finrank ℝ Dᗮ = Module.finrank ℝ Rᗮ := by
  have hD := D.finrank_add_finrank_orthogonal
  have hR := R.finrank_add_finrank_orthogonal
  have hDR := U.toLinearEquiv.finrank_eq
  omega

/-- A complement isometry is constructed from finite orthonormal bases, not assumed. -/
def canonicalComplement (U : D ≃ₗᵢ[ℝ] R)
    (hEF : Module.finrank ℝ E = Module.finrank ℝ F) : Dᗮ ≃ₗᵢ[ℝ] Rᗮ :=
  (stdOrthonormalBasis ℝ Dᗮ).repr.trans
    ((stdOrthonormalBasis ℝ Rᗮ).reindex
      (finCongr (complement_finrank_eq D R U hEF).symm)).repr.symm

/-- One full extension, constructed for every partial isometry in equal ambient dimensions. -/
def canonicalCompletion (U : D ≃ₗᵢ[ℝ] R)
    (hEF : Module.finrank ℝ E = Module.finrank ℝ F) : E ≃ₗᵢ[ℝ] F :=
  completion D R U (canonicalComplement D R U hEF)

 theorem canonicalCompletion_extends (U : D ≃ₗᵢ[ℝ] R)
    (hEF : Module.finrank ℝ E = Module.finrank ℝ F) :
    ExtendsPartial D R U (canonicalCompletion D R U hEF) :=
  completion_extends D R U _

 theorem exists_completion (U : D ≃ₗᵢ[ℝ] R)
    (hEF : Module.finrank ℝ E = Module.finrank ℝ F) :
    ∃ Q : E ≃ₗᵢ[ℝ] F, ExtendsPartial D R U Q :=
  ⟨canonicalCompletion D R U hEF, canonicalCompletion_extends D R U hEF⟩

/-- Relative to a constructed completion, every other completion differs by a domain stabilizer. -/
theorem relativeCompletion_fixes_domain (U : D ≃ₗᵢ[ℝ] R)
    (hEF : Module.finrank ℝ E = Module.finrank ℝ F)
    (Q : E ≃ₗᵢ[ℝ] F) (hQ : ExtendsPartial D R U Q) (x : D) :
    (Q.trans (canonicalCompletion D R U hEF).symm) (x : E) = (x : E) := by
  change (canonicalCompletion D R U hEF).symm (Q (x : E)) = (x : E)
  rw [hQ]
  have h := extension_symm D R U (canonicalCompletion D R U hEF)
    (canonicalCompletion_extends D R U hEF) (U x)
  simpa using h

/-- Exact pointwise factorization through that stabilizer and the constructed completion. -/
theorem relativeCompletion_factorization (U : D ≃ₗᵢ[ℝ] R)
    (hEF : Module.finrank ℝ E = Module.finrank ℝ F) (Q : E ≃ₗᵢ[ℝ] F) (x : E) :
    ((Q.trans (canonicalCompletion D R U hEF).symm).trans
      (canonicalCompletion D R U hEF)) x = Q x := by simp

/-- The inverse of a glued completion is the gluing of the two inverse isometries. -/
theorem completion_symm_apply (U : D ≃ₗᵢ[ℝ] R) (V : Dᗮ ≃ₗᵢ[ℝ] Rᗮ) (y : F) :
    (completion D R U V).symm y =
      (U.symm (R.orthogonalProjectionOnto y) : E) +
        (V.symm (Rᗮ.orthogonalProjectionOnto y) : E) := by
  apply (completion D R U V).injective
  rw [LinearIsometryEquiv.apply_symm_apply, map_add, completion_on_domain,
    completion_on_complement]
  simp only [LinearIsometryEquiv.apply_symm_apply]
  simpa using (R.orthogonalDecomposition.symm_apply_apply y).symm

/-- Every completion splits a forward reveal into its prescribed and unprescribed parts. -/
theorem extension_apply (U : D ≃ₗᵢ[ℝ] R) (Q : E ≃ₗᵢ[ℝ] F)
    (hQ : ExtendsPartial D R U Q) (x : E) :
    Q x = (U (D.orthogonalProjectionOnto x) : F) +
      Q (Dᗮ.orthogonalProjectionOnto x : E) := by
  rw [← completion_complementRestriction_apply D R U Q hQ x, completion_apply]
  rfl

/-- The corresponding exact inverse-reveal formula. -/
theorem extension_symm_apply (U : D ≃ₗᵢ[ℝ] R) (Q : E ≃ₗᵢ[ℝ] F)
    (hQ : ExtendsPartial D R U Q) (y : F) :
    Q.symm y = (U.symm (R.orthogonalProjectionOnto y) : E) +
      Q.symm (Rᗮ.orthogonalProjectionOnto y : F) :=
  extension_apply R D U.symm Q.symm (extension_symm D R U Q hQ) y

/-- The group-theoretic domain stabilizer, represented by its exact pointwise constraint. -/
def DomainStabilizer := {S : E ≃ₗᵢ[ℝ] E // ∀ x : D, S (x : E) = (x : E)}

/-- After choosing the constructed completion, its full fiber is exactly a stabilizer torsor. -/
def stabilizerEquiv (U : D ≃ₗᵢ[ℝ] R)
    (hEF : Module.finrank ℝ E = Module.finrank ℝ F) :
    DomainStabilizer D ≃ {Q : E ≃ₗᵢ[ℝ] F // ExtendsPartial D R U Q} where
  toFun S := ⟨S.val.trans (canonicalCompletion D R U hEF), by
    intro x
    change canonicalCompletion D R U hEF (S.val (x : E)) = (U x : F)
    rw [S.property x]
    exact canonicalCompletion_extends D R U hEF x⟩
  invFun Q := ⟨Q.val.trans (canonicalCompletion D R U hEF).symm,
    relativeCompletion_fixes_domain D R U hEF Q.val Q.property⟩
  left_inv S := by
    apply Subtype.ext
    apply LinearIsometryEquiv.ext
    intro x
    simp
  right_inv Q := by
    apply Subtype.ext
    apply LinearIsometryEquiv.ext
    intro x
    simp

/-- The actual linear adjoint, hence the Euclidean transpose, has the prescribed inverse values. -/
theorem extension_adjoint_data (U : D ≃ₗᵢ[ℝ] R) (Q : E ≃ₗᵢ[ℝ] F)
    (hQ : ExtendsPartial D R U Q) (y : R) :
    LinearMap.adjoint Q.toLinearMap (y : F) = (U.symm y : E) := by
  rw [Q.adjoint_toLinearMap_eq_symm]
  exact extension_symm D R U Q hQ y

end NCConcave16991.PartialIsometry


