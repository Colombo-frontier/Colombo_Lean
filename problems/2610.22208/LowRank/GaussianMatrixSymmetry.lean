import LowRank.GaussianMatrixRows

/-! Explicit product-measure proofs of invariance under signed row changes
and row permutations. These finite symmetries suffice for projection means. -/

namespace LowRank
open MeasureTheory ProbabilityTheory
noncomputable section

theorem gaussianReal_sign_preserving (a : ℝ) (ha : a * a = 1) (v : NNReal) :
    MeasurePreserving (fun x : ℝ => a * x) (gaussianReal 0 v) (gaussianReal 0 v) := by
  refine ⟨measurable_const.mul measurable_id, ?_⟩
  have hsq : (⟨a ^ 2, sq_nonneg a⟩ : NNReal) = 1 := by
    apply NNReal.eq
    simpa only [NNReal.coe_mk, NNReal.coe_one, pow_two] using ha
  simpa only [mul_zero, hsq, one_mul] using (gaussianReal_map_const_mul (μ := 0) (v := v) a)

theorem iidVectorLaw_sign_preserving (s : ℕ) (a : ℝ) (ha : a * a = 1) (v : NNReal) :
    MeasurePreserving (fun z : Fin s → ℝ => fun j => a * z j) (iidVectorLaw s v) (iidVectorLaw s v) :=
  measurePreserving_pi (fun _ : Fin s => gaussianReal 0 v) (fun _ => gaussianReal 0 v)
    (fun _ => gaussianReal_sign_preserving a ha v)

theorem iidMatrixLaw_signed_rows_preserving (r s : ℕ) (a : Fin r → ℝ)
    (ha : ∀ i, a i * a i = 1) (v : NNReal) :
    MeasurePreserving (fun D : Matrix (Fin r) (Fin s) ℝ => fun i j => a i * D i j)
      (iidMatrixLaw r s v) (iidMatrixLaw r s v) :=
  measurePreserving_pi (fun _ : Fin r => iidVectorLaw s v) (fun _ => iidVectorLaw s v)
    (fun i => iidVectorLaw_sign_preserving s (a i) (ha i) v)

theorem iidMatrixLaw_reindex_rows_preserving (r s : ℕ) (e : Fin r ≃ Fin r) (v : NNReal) :
    MeasurePreserving (fun D : Matrix (Fin r) (Fin s) ℝ => D.submatrix e id)
      (iidMatrixLaw r s v) (iidMatrixLaw r s v) := by
  have h := measurePreserving_piCongrLeft (fun _ : Fin r => iidVectorLaw s v) e.symm
  convert h using 1
  funext D i j
  simp [MeasurableEquiv.coe_piCongrLeft, Matrix.submatrix_apply, Equiv.piCongrLeft_apply]

end
end LowRank
