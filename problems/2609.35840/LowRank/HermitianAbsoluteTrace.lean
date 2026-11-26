import LowRank.SymmetricFunctionTrace

/-! Absolute spectral power for symmetric matrices and its convex pinching
inequality for every exponent at least one. -/

namespace LowRank
open Matrix
open scoped Matrix BigOperators
noncomputable section

def symmetricAbsPowerTrace {d : ℕ} {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.IsHermitian) (p : ℝ) : ℝ := symmetricFunctionTrace hH (fun x => |x| ^ p)

theorem convexOn_abs_rpow {p : ℝ} (hp : 1 ≤ p) :
    ConvexOn ℝ Set.univ (fun x : ℝ => |x| ^ p) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ s t hs ht hst
  have hab : |s * x + t * y| ≤ s * |x| + t * |y| := by
    calc
      _ ≤ |s * x| + |t * y| := abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg hs, abs_of_nonneg ht]
  have hc := (convexOn_rpow hp).2 (x := |x|) (y := |y|) (abs_nonneg x) (abs_nonneg y) hs ht hst
  exact (Real.rpow_le_rpow (abs_nonneg _) hab (by linarith)).trans hc

theorem symmetricAbsPowerTrace_congr {d : ℕ} {H K : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.IsHermitian) (hK : K.IsHermitian) (he : H = K) (p : ℝ) :
    symmetricAbsPowerTrace hH p = symmetricAbsPowerTrace hK p :=
  symmetricFunctionTrace_congr hH hK he _

theorem symmetricAbsPowerTrace_eq_schattenPower {d : ℕ} {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.IsHermitian) (p : ℝ) : symmetricAbsPowerTrace hH p = schattenPower p H := by
  let sp := orderedMatrixSpectrum hH
  have hHt : Hᵀ = H := by simpa only [conjTranspose_eq_transpose_of_trivial] using hH.eq
  have hd : sp.basisᵀ * (Hᵀ * H) * sp.basis = diagonal (fun i => sp.value i ^ 2) := by
    simpa only [hHt, pow_two] using sp.diagonalizes_pow 2
  rw [symmetricAbsPowerTrace, symmetricFunctionTrace_eq hH sp,
    schattenPower_eq_symmetricPowerTrace,
    symmetricPowerTrace_eq_of_diagonalization _ _ sp.basis sp.orthogonal hd]
  apply Finset.sum_congr rfl
  intro i _
  have he : (sp.value i ^ 2) ^ (p / 2) = |sp.value i| ^ p := by
    calc
      _ = ((sp.value i ^ 2) ^ (1 / 2 : ℝ)) ^ p := by
        rw [← Real.rpow_mul (sq_nonneg _)]
        congr 1
        ring
      _ = (Real.sqrt (sp.value i ^ 2)) ^ p := by rw [Real.sqrt_eq_rpow]
      _ = _ := by rw [Real.sqrt_sq_eq_abs]
  exact he.symm

theorem symmetricAbsPowerTrace_projector_pinching {d : ℕ}
    {H P : Matrix (Fin d) (Fin d) ℝ} (hH : H.IsHermitian) (hP : IsOrthogonalProjector P)
    {p : ℝ} (hp : 1 ≤ p) :
    symmetricAbsPowerTrace (projectorSandwich_isHermitian hH hP) p +
      symmetricAbsPowerTrace (projectorSandwich_isHermitian hH hP.complement) p ≤
        symmetricAbsPowerTrace hH p :=
  symmetricFunctionTrace_projector_pinching hH hP (convexOn_abs_rpow hp)
    (by simp only [abs_zero, Real.zero_rpow (by linarith : p ≠ 0)])

end
end LowRank
