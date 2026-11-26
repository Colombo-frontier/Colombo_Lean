import LowRank.GaussianOrthogonalCompression
import LowRank.ProjectorBasis
import LowRank.KernelProjectorGram

/-! Squared lengths of Gaussian projections depend only on the projector
rank. The resulting law is defined as a sum of independent squared normals. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix
noncomputable section

def squaredGaussianLaw (m : ℕ) (v : NNReal) : Measure ℝ :=
  (iidVectorLaw m v).map (fun z => z ⬝ᵥ z)

theorem measurable_dot_self (m : ℕ) : Measurable (fun z : Fin m → ℝ => z ⬝ᵥ z) := by
  simp only [dotProduct]
  fun_prop

instance squaredGaussianLaw_probability (m : ℕ) (v : NNReal) :
    IsProbabilityMeasure (squaredGaussianLaw m v) :=
  isProbabilityMeasure_map (measurable_dot_self m).aemeasurable

theorem iidVectorLaw_projector_quadratic {d m : ℕ}
    (P : Matrix (Fin d) (Fin d) ℝ) (hP : IsOrthogonalProjector P) (hrank : P.rank = m)
    (v : NNReal) :
    (iidVectorLaw d v).map (fun x => x ⬝ᵥ (P *ᵥ x)) = squaredGaussianLaw m v := by
  obtain ⟨B, hB, hBB⟩ := projector_basis_factorization hP hrank
  have he (x : Fin d → ℝ) : x ⬝ᵥ (P *ᵥ x) = (Bᵀ *ᵥ x) ⬝ᵥ (Bᵀ *ᵥ x) := by
    rw [← hBB, ← Matrix.mulVec_mulVec, dotProduct_mulVec, ← Matrix.mulVec_transpose]
  simp_rw [he]
  have hm : Measurable (fun x : Fin d → ℝ => Bᵀ *ᵥ x) := by
    apply measurable_pi_lambda
    intro i
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  change (iidVectorLaw d v).map ((fun z : Fin m → ℝ => z ⬝ᵥ z) ∘ (fun x => Bᵀ *ᵥ x)) = _
  rw [← Measure.map_map (measurable_dot_self m) hm, iidVectorLaw_orthogonal_compression B hB]
  rfl

theorem leftKernelProjector_rank_full {d s : ℕ} (Y : Matrix (Fin d) (Fin s) ℝ)
    (hY : Function.Injective Y.mulVec) (hs : s ≤ d) : (leftKernelProjector Y).rank = d - s := by
  have h := (leftKernelProjector_isProjector Y).trace_eq_rank.symm.trans (leftKernelProjector_trace Y hY)
  simp only [Fintype.card_fin, ← Nat.cast_sub hs] at h
  exact_mod_cast h

theorem iidVectorLaw_kernel_quadratic {d s : ℕ} (Y : Matrix (Fin d) (Fin s) ℝ)
    (hY : Function.Injective Y.mulVec) (hs : s ≤ d) (v : NNReal) :
    (iidVectorLaw d v).map (fun x => x ⬝ᵥ (leftKernelProjector Y *ᵥ x)) = squaredGaussianLaw (d - s) v :=
  iidVectorLaw_projector_quadratic _ (leftKernelProjector_isProjector Y)
    (leftKernelProjector_rank_full Y hY hs) v

end
end LowRank
