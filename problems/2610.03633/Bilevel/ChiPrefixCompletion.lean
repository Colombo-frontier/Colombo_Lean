import Bilevel.ChiPrefixReadout
import Bilevel.PrimitiveGeometry
import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-! Explicit completion in an auxiliary Hilbert block. Only disclosed
columns and their prefix Gram identities are used. The undisclosed tail is
the image of a fixed public isometry into the auxiliary space. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Bilevel.ChiPrefixEvaluation
open ChiBoundedChain PrimitiveGeometry WrappedChain
variable {E A : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]

def completedColumn (n r : ℕ) (columns : Fin (n+1) → E) (V : Space n →ₗᵢ[ℝ] A)
    (k : Fin (n+1)) : Joint E A :=
  if k.val<r then pack (columns k) 0 else pack 0 (V (basis k))

omit [CompleteSpace E] [CompleteSpace A] in
theorem completedColumn_orthonormal (n r : ℕ) (columns : Fin (n+1) → E) (V : Space n →ₗᵢ[ℝ] A)
    (hGram : ∀ i j : Fin (n+1),i.val<r → j.val<r → ⟪columns i,columns j⟫=if i=j then 1 else 0) :
    Orthonormal ℝ (completedColumn n r columns V) := by
  rw [orthonormal_iff_ite]
  intro i j
  by_cases hi : i.val<r <;> by_cases hj : j.val<r
  · simpa [completedColumn,hi,hj,WithLp.prod_inner_apply,pack] using hGram i j hi hj
  · have hij : i≠j := by intro he;subst j;contradiction
    simp [completedColumn,hi,hj,WithLp.prod_inner_apply,pack,hij]
  · have hij : i≠j := by intro he;subst j;contradiction
    simp [completedColumn,hi,hj,WithLp.prod_inner_apply,pack,hij]
  · simp [completedColumn,hi,hj,WithLp.prod_inner_apply,pack,V.inner_map_map,basis,
      EuclideanSpace.inner_single_left,EuclideanSpace.single_apply]

def completionLinear (n r : ℕ) (columns : Fin (n+1) → E) (V : Space n →ₗᵢ[ℝ] A) :
    Space n →L[ℝ] Joint E A :=
  ∑ k : Fin (n+1),(EuclideanSpace.proj (𝕜:=ℝ) k).smulRight (completedColumn n r columns V k)

omit [CompleteSpace E] [CompleteSpace A] in
theorem completionLinear_basis (n r : ℕ) (columns : Fin (n+1) → E) (V : Space n →ₗᵢ[ℝ] A)
    (k : Fin (n+1)) : completionLinear n r columns V (basis k)=completedColumn n r columns V k := by
  simp [completionLinear,ContinuousLinearMap.sum_apply,basis,EuclideanSpace.single_apply]

def completionFrame (n r : ℕ) (columns : Fin (n+1) → E) (V : Space n →ₗᵢ[ℝ] A)
    (hGram : ∀ i j : Fin (n+1),i.val<r → j.val<r → ⟪columns i,columns j⟫=if i=j then 1 else 0) :
    Space n →ₗᵢ[ℝ] Joint E A :=
  (completionLinear n r columns V).toLinearMap.isometryOfOrthonormal
    (v := (EuclideanSpace.basisFun (Fin (n+1)) ℝ).toBasis)
    (EuclideanSpace.basisFun (Fin (n+1)) ℝ).orthonormal (by
      have he : ((completionLinear n r columns V).toLinearMap ∘
          (EuclideanSpace.basisFun (Fin (n+1)) ℝ).toBasis)=completedColumn n r columns V := by
        funext k
        change completionLinear n r columns V ((EuclideanSpace.basisFun (Fin (n+1)) ℝ) k)=_
        rw [EuclideanSpace.basisFun_apply]
        exact completionLinear_basis n r columns V k
      rw [he]
      exact completedColumn_orthonormal n r columns V hGram)

omit [CompleteSpace E] [CompleteSpace A] in
theorem completionFrame_basis (n r : ℕ) (columns : Fin (n+1) → E) (V : Space n →ₗᵢ[ℝ] A)
    (hGram : ∀ i j : Fin (n+1),i.val<r → j.val<r → ⟪columns i,columns j⟫=if i=j then 1 else 0)
    (k : Fin (n+1)) : completionFrame n r columns V hGram (basis k)=completedColumn n r columns V k :=
  completionLinear_basis n r columns V k

omit [CompleteSpace E] [CompleteSpace A] in
theorem norm_pack_zero (u : E) : ‖pack u (0:A)‖=‖u‖ := by
  simp only [norm_pack,norm_zero,zero_pow (by norm_num : 2≠0),add_zero,Real.sqrt_sq (norm_nonneg u)]

omit [CompleteSpace E] [CompleteSpace A] in
theorem compress_pack_zero (R : ℝ) (u : E) :
    RadialWrapper.compress R (pack u (0:A))=pack (RadialWrapper.compress R u) 0 := by
  have he : RadialWrapper.scale R (pack u (0:A))=RadialWrapper.scale R u := by
    simp only [RadialWrapper.scale,norm_pack_zero]
  change pack (RadialWrapper.scale R (pack u (0:A)) • u)
    (RadialWrapper.scale R (pack u (0:A)) • (0:A))=pack (RadialWrapper.scale R u • u) 0
  rw [he,smul_zero]

theorem completion_coordinates (n r : ℕ) (R : ℝ) (columns : Fin (n+1) → E)
    (V : Space n →ₗᵢ[ℝ] A)
    (hGram : ∀ i j : Fin (n+1),i.val<r → j.val<r → ⟪columns i,columns j⟫=if i=j then 1 else 0)
    (u : E) :
    coordinates n R (completionFrame n r columns V hGram) (pack u (0:A))=readout n r R columns u := by
  ext k
  rw [coordinates_inner,completionFrame_basis,compress_pack_zero,readout_apply]
  by_cases hk : k.val<r <;> simp [completedColumn,hk,WithLp.prod_inner_apply,pack]

theorem completed_restriction_eq (n r : ℕ) (R : ℝ) (columns : Fin (n+1) → E)
    (V : Space n →ₗᵢ[ℝ] A)
    (hGram : ∀ i j : Fin (n+1),i.val<r → j.val<r → ⟪columns i,columns j⟫=if i=j then 1 else 0)
    (f : Space n → ℝ) (u : E) :
    f (coordinates n R (completionFrame n r columns V hGram) (pack u (0:A)))=
      disclosedEvaluator n r R columns f u :=
  congrArg f (completion_coordinates n r R columns V hGram u)

end Bilevel.ChiPrefixEvaluation
