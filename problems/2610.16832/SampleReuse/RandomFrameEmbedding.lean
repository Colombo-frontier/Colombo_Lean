import SampleReuse.RandomFramePrefixLoss

noncomputable section
namespace SampleReuse.RandomFrame

open SecondOrder RandomizedFO2003 Rotations

theorem blockUnit_one_eq_single {m : ℕ} (i : Fin m) :
    blockUnit i (1:ℝ) = EuclideanSpace.single i (1:ℝ) := by
  ext j
  by_cases hij : j = i
  · simp only [blockUnit_apply, EuclideanSpace.single_apply, if_pos hij]
  · simp only [blockUnit_apply, EuclideanSpace.single_apply, if_neg hij]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Convert an actual orthonormal family into the linear isometry used by the
hard scalar loss, using the Euclidean orthonormal basis. -/
def embeddingOfFrame {m : ℕ} (e : Fin m → E) (he : Orthonormal ℝ e) : Point m →ₗᵢ[ℝ] E := by
  let b := EuclideanSpace.basisFun (Fin m) ℝ
  let L : Point m →ₗ[ℝ] E := b.toBasis.constr ℝ e
  apply L.isometryOfOrthonormal (v := b.toBasis)
  · exact b.orthonormal
  · simpa only [Function.comp_def, L, Basis.constr_basis] using he

theorem embeddingOfFrame_column {m : ℕ} (e : Fin m → E) (he : Orthonormal ℝ e) (i : Fin m) :
    embeddingOfFrame e he (blockUnit i (1:ℝ)) = e i := by
  rw [blockUnit_one_eq_single, ← EuclideanSpace.basisFun_apply]
  exact (EuclideanSpace.basisFun (Fin m) ℝ).toBasis.constr_basis ℝ e i

theorem embedding_columns_orthonormal {m : ℕ} (U : Point m →ₗᵢ[ℝ] E) :
    Orthonormal ℝ (fun i : Fin m => U (blockUnit i (1:ℝ))) := by
  simpa only [Function.comp_def, blockUnit_one_eq_single] using
    (EuclideanSpace.orthonormal_single (𝕜 := ℝ) (ι := Fin m)).comp_linearIsometry U

def standardEmbedding {m d : ℕ} (hmd : m ≤ d) : Point m →ₗᵢ[ℝ] Point d :=
  embeddingOfFrame (fun i : Fin m => EuclideanSpace.single (Fin.castLE hmd i) (1:ℝ))
    ((EuclideanSpace.orthonormal_single (𝕜 := ℝ) (ι := Fin d)).comp
      (Fin.castLE hmd) (Fin.castLE_injective hmd))

def rotatedEmbedding {m d : ℕ} (U : Point m →ₗᵢ[ℝ] Point d) (V : Rotation (Point d)) :
    Point m →ₗᵢ[ℝ] Point d := (isometry (Point d) V).toLinearIsometry.comp U

@[simp] theorem rotatedEmbedding_column {m d : ℕ} (U : Point m →ₗᵢ[ℝ] Point d)
    (V : Rotation (Point d)) (i : Fin m) :
    rotatedEmbedding U V (blockUnit i (1:ℝ)) = isometry (Point d) V (U (blockUnit i (1:ℝ))) := rfl

end SampleReuse.RandomFrame
