import LowRank.GaussianMatrixTranspose
import LowRank.GaussianOrthogonalCompression

/-! Orthogonal compression of either dimension of an actual iid Gaussian
matrix preserves its Gaussian law, with the compressed matrix dimensions. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix
noncomputable section

theorem iidMatrixLaw_right_compression {r d k : ℕ}
    (V : Matrix (Fin d) (Fin k) ℝ) (hV : Vᵀ * V = 1) (v : NNReal) :
    (iidMatrixLaw r d v).map (fun X => X * V) = iidMatrixLaw r k v := by
  have hm : Measurable (fun x : Fin d → ℝ => Vᵀ *ᵥ x) := by
    apply measurable_pi_lambda
    intro i
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  have hp := measurePreserving_pi (fun _ : Fin r => iidVectorLaw d v)
    (fun _ : Fin r => iidVectorLaw k v)
    (fun _ => (show MeasurePreserving (fun x => Vᵀ *ᵥ x) (iidVectorLaw d v) (iidVectorLaw k v) from
      ⟨hm, iidVectorLaw_orthogonal_compression V hV v⟩))
  convert hp.map_eq using 2
  funext X i j
  simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_comm]

theorem iidMatrixLaw_left_compression {r d k : ℕ}
    (V : Matrix (Fin d) (Fin k) ℝ) (hV : Vᵀ * V = 1) (v : NNReal) :
    (iidMatrixLaw d r v).map (fun X => Vᵀ * X) = iidMatrixLaw k r v := by
  have hp : MeasurePreserving (fun X : Matrix (Fin r) (Fin d) ℝ => X * V)
      (iidMatrixLaw r d v) (iidMatrixLaw r k v) :=
    ⟨(by fun_prop : Continuous (fun X : Matrix (Fin r) (Fin d) ℝ => X * V)).measurable,
      iidMatrixLaw_right_compression V hV v⟩
  have h := ((iidMatrixLaw_transpose_preserving r k v).comp
    (hp.comp (iidMatrixLaw_transpose_preserving d r v))).map_eq
  simpa only [Function.comp_def, Matrix.transpose_mul, Matrix.transpose_transpose] using h

theorem iidMatrixLaw_left_compression_preserving {r d k : ℕ}
    (V : Matrix (Fin d) (Fin k) ℝ) (hV : Vᵀ * V = 1) (v : NNReal) :
    MeasurePreserving (fun X : Matrix (Fin d) (Fin r) ℝ => Vᵀ * X)
      (iidMatrixLaw d r v) (iidMatrixLaw k r v) :=
  ⟨(by fun_prop : Continuous (fun X : Matrix (Fin d) (Fin r) ℝ => Vᵀ * X)).measurable,
    iidMatrixLaw_left_compression V hV v⟩

end
end LowRank
