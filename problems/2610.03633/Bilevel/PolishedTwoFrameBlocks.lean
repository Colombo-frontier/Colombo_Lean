import Bilevel.ChiBoundedChain
import Bilevel.HaarFrame

/-! Linear isometric frames for the source prior. All micro blocks are
restrictions of ONE global orthonormal S*M-column frame. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.PolishedTwoFrameBlocks
open ChiBoundedChain
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def frameLinear (n : ℕ) (V : Fin (n+1) → E) : Space n →L[ℝ] E :=
  ∑ k : Fin (n+1),(EuclideanSpace.proj (𝕜:=ℝ) k).smulRight (V k)

theorem frameLinear_basis (n : ℕ) (V : Fin (n+1) → E) (j : Fin (n+1)) :
    frameLinear n V (basis j)=V j := by
  simp [frameLinear,ContinuousLinearMap.sum_apply,basis,EuclideanSpace.single_apply]

def ofFrame (n : ℕ) (V : Fin (n+1) → E) (hV : Orthonormal ℝ V) : Space n →ₗᵢ[ℝ] E :=
  (frameLinear n V).toLinearMap.isometryOfOrthonormal
    (v := (EuclideanSpace.basisFun (Fin (n+1)) ℝ).toBasis)
    (EuclideanSpace.basisFun (Fin (n+1)) ℝ).orthonormal (by
      have he : (frameLinear n V).toLinearMap ∘ (EuclideanSpace.basisFun (Fin (n+1)) ℝ).toBasis=V := by
        funext j
        rw [Function.comp_apply]
        change frameLinear n V ((EuclideanSpace.basisFun (Fin (n+1)) ℝ) j)=_
        rw [EuclideanSpace.basisFun_apply]
        exact frameLinear_basis n V j
      rw [he]
      exact hV)

theorem ofFrame_basis (n : ℕ) (V : Fin (n+1) → E) (hV : Orthonormal ℝ V) (j : Fin (n+1)) :
    ofFrame n V hV (basis j)=V j := frameLinear_basis n V j

def blockColumns {S n : ℕ} (V : Fin (S*(n+1)) → E) (i : Fin S) : Fin (n+1) → E :=
  fun j => V (finProdFinEquiv (i,j))

theorem blockColumns_orthonormal {S n : ℕ} (V : Fin (S*(n+1)) → E)
    (hV : Orthonormal ℝ V) (i : Fin S) : Orthonormal ℝ (blockColumns V i) := by
  apply hV.comp (fun j => finProdFinEquiv (i,j))
  intro j k he
  exact (Prod.mk.inj (finProdFinEquiv.injective he)).2

def microBlockFrame {S n : ℕ} (V : Fin (S*(n+1)) → E) (hV : Orthonormal ℝ V) (i : Fin S) :
    Space n →ₗᵢ[ℝ] E := ofFrame n (blockColumns V i) (blockColumns_orthonormal V hV i)

theorem microBlockFrame_basis {S n : ℕ} (V : Fin (S*(n+1)) → E) (hV : Orthonormal ℝ V)
    (i : Fin S) (j : Fin (n+1)) :
    microBlockFrame V hV i (basis j)=V (finProdFinEquiv (i,j)) := ofFrame_basis _ _ _ _

def haarMacroFrame {d n : ℕ} (h : n+1≤d) (A : OrthogonalHaar.Group d) :
    Space n →ₗᵢ[ℝ] EuclideanGaussian.Space d :=
  ofFrame n (HaarFrame.frame d (n+1) h A) (HaarFrame.frame_orthonormal d (n+1) h A)

def haarMicroBlockFrame {d S n : ℕ} (h : S*(n+1)≤d) (A : OrthogonalHaar.Group d) (i : Fin S) :
    Space n →ₗᵢ[ℝ] EuclideanGaussian.Space d :=
  microBlockFrame (HaarFrame.frame d (S*(n+1)) h A) (HaarFrame.frame_orthonormal d (S*(n+1)) h A) i

theorem haarMacroFrame_basis {d n : ℕ} (h : n+1≤d) (A : OrthogonalHaar.Group d) (j : Fin (n+1)) :
    haarMacroFrame h A (basis j)=HaarFrame.frame d (n+1) h A j := ofFrame_basis _ _ _ _

theorem haarMicroBlockFrame_basis {d S n : ℕ} (h : S*(n+1)≤d) (A : OrthogonalHaar.Group d)
    (i : Fin S) (j : Fin (n+1)) :
    haarMicroBlockFrame h A i (basis j)=HaarFrame.frame d (S*(n+1)) h A (finProdFinEquiv (i,j)) :=
  microBlockFrame_basis _ _ _ _

end Bilevel.PolishedTwoFrameBlocks
