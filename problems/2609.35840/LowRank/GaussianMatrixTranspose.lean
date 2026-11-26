import LowRank.GaussianMatrixRows

/-! Transposition preserves the iid Gaussian matrix law. The proof uses exact
row and column product decompositions, including empty matrix dimensions. -/

namespace LowRank
open MeasureTheory
open scoped Matrix
noncomputable section

theorem iidMatrixLaw_transpose_preserving (r s : ℕ) (v : NNReal) :
    MeasurePreserving (Matrix.transpose : Matrix (Fin r) (Fin s) ℝ → _)
      (iidMatrixLaw r s v) (iidMatrixLaw s r v) := by
  induction s with
  | zero =>
    have hm : Measurable (Matrix.transpose : Matrix (Fin r) (Fin 0) ℝ → _) := by fun_prop
    refine ⟨hm, ?_⟩
    ext t ht
    rw [Measure.map_apply hm ht]
    by_cases hne : t.Nonempty
    · obtain ⟨x, hx⟩ := hne
      have heq : t = Set.univ := Set.eq_univ_of_forall (fun y => (Subsingleton.elim x y) ▸ hx)
      rw [heq]
      simp
    · rw [Set.not_nonempty_iff_eq_empty.mp hne]
      simp
  | succ s ih =>
    have hcol := splitFirstColumn_preserving r s v
    have hprod : MeasurePreserving
        (fun p : (Fin r → ℝ) × Matrix (Fin r) (Fin s) ℝ => (p.1, p.2ᵀ))
        ((iidVectorLaw r v).prod (iidMatrixLaw r s v))
        ((iidVectorLaw r v).prod (iidMatrixLaw s r v)) :=
      (MeasurePreserving.id (iidVectorLaw r v)).prod ih
    have hrow := measurePreserving_piFinSuccAbove
      (fun _ : Fin (s + 1) => iidVectorLaw r v) 0
    have hjoin := hrow.symm (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (s + 1) => Fin r → ℝ) 0)
    convert hjoin.comp (hprod.comp hcol) using 1
    funext X
    apply (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (s + 1) => Fin r → ℝ) 0).injective
    simp only [Function.comp_def, MeasurableEquiv.apply_symm_apply]
    rfl

end
end LowRank
