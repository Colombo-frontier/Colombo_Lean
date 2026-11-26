import Bilevel.ChiSourceAuxiliaryDimension
import Bilevel.ChiPrefixReadout
import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-! Fixed public coordinate embeddings into one finite auxiliary Hilbert
space for every source level. They do not use hidden or disclosed frames. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiPrefixEvaluation
open ChiBoundedChain ChiRecursive ChiCurvatureSchedule ChiExtensionCalibration

def auxiliaryLinear (n N : ℕ) (h : n+1≤N) : Space n →L[ℝ] EuclideanSpace ℝ (Fin N) :=
  ∑ k : Fin (n+1),(EuclideanSpace.proj (𝕜:=ℝ) k).smulRight (EuclideanSpace.single (Fin.castLE h k) 1)

theorem auxiliaryLinear_basis (n N : ℕ) (h : n+1≤N) (k : Fin (n+1)) :
    auxiliaryLinear n N h (basis k)=EuclideanSpace.single (Fin.castLE h k) 1 := by
  simp [auxiliaryLinear,ContinuousLinearMap.sum_apply,basis,EuclideanSpace.single_apply]

def auxiliaryFrame (n N : ℕ) (h : n+1≤N) : Space n →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N) :=
  (auxiliaryLinear n N h).toLinearMap.isometryOfOrthonormal
    (v := (EuclideanSpace.basisFun (Fin (n+1)) ℝ).toBasis)
    (EuclideanSpace.basisFun (Fin (n+1)) ℝ).orthonormal (by
      have he : ((auxiliaryLinear n N h).toLinearMap ∘
          (EuclideanSpace.basisFun (Fin (n+1)) ℝ).toBasis)=
          (fun k : Fin (n+1) => EuclideanSpace.single (Fin.castLE h k) (1:ℝ)) := by
        funext k
        change auxiliaryLinear n N h ((EuclideanSpace.basisFun (Fin (n+1)) ℝ) k)=_
        rw [EuclideanSpace.basisFun_apply]
        exact auxiliaryLinear_basis n N h k
      rw [he]
      exact EuclideanSpace.orthonormal_single.comp (Fin.castLE h) (Fin.castLE_injective h))

theorem auxiliaryFrame_basis (n N : ℕ) (h : n+1≤N) (k : Fin (n+1)) :
    auxiliaryFrame n N h (basis k)=EuclideanSpace.single (Fin.castLE h k) 1 :=
  auxiliaryLinear_basis n N h k

def sourceAuxiliaryFrame (cn η T Kg : ℝ) (hcn : 0≤cn) (hT : 1≤T) (j : ℕ) :
    Space (sourceChainIndex cn (sourceRatio T j) (resolution η Kg j)) →ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (sourceAuxiliaryDimension cn η T Kg)) :=
  auxiliaryFrame _ _ (source_chain_size_le_auxiliary hcn hT η Kg j)

end Bilevel.ChiPrefixEvaluation
