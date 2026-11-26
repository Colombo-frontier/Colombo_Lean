import Matvec.DilationSpectrum
import Matvec.RandomOrthogonal

/-! Explicit finite-dimensional coordinate equivalences used to transport
source solvers to the Gaussian dilation without additional oracle calls. -/
namespace Matvec
noncomputable section

def dilationIndexEquiv (N : ℕ) {ι : Type*} [Fintype ι]
    (hcard : Fintype.card ι = 2 * N) : (Fin N ⊕ Fin N) ≃ ι :=
  Fintype.equivOfCardEq (by simp only [Fintype.card_sum, Fintype.card_fin]; omega)

def dilationCoordinateIsometry (N : ℕ) {ι : Type*} [Fintype ι]
    (hcard : Fintype.card ι = 2 * N) :
    DilationSpace N ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (dilationIndexEquiv N hcard)

def dilationFinIsometry (N : ℕ) : DilationSpace N ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (2 * N)) :=
  dilationCoordinateIsometry N (Fintype.card_fin _)

theorem cube_succ_card (k : ℕ) : Fintype.card (RandomOrthogonal.Cube (k + 1)) = 2 * 2 ^ k := by
  simp only [RandomOrthogonal.Cube, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, pow_succ]
  omega

def dilationCubeIsometry (k : ℕ) :
    DilationSpace (2 ^ k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (RandomOrthogonal.Cube (k + 1)) :=
  dilationCoordinateIsometry (2 ^ k) (cube_succ_card k)

def ballRowEquiv (N : ℕ) : Fin (4 * N) ≃ (Fin (2 * N) ⊕ Fin (2 * N)) :=
  Fintype.equivOfCardEq (by simp only [Fintype.card_sum, Fintype.card_fin]; omega)

def ballColumnEquiv (N : ℕ) : Fin (2 * N + 1) ≃ (Fin (2 * N) ⊕ Unit) :=
  Fintype.equivOfCardEq (by simp)

def simplexCubeEquiv (k : ℕ) : Fin (4 * 2 ^ k) ≃
    (RandomOrthogonal.Cube (k + 1) ⊕ RandomOrthogonal.Cube (k + 1)) :=
  Fintype.equivOfCardEq (by simp only [Fintype.card_fin, Fintype.card_sum, cube_succ_card]; omega)

end
end Matvec
