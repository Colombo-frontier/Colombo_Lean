import LowRank.GaussianQueryAlgebra

/-! A nonzero linear functional of a positive-variance iid Gaussian vector
has no atoms. Consequently a nonzero matrix coefficient times a Gaussian
block with at least one column almost surely misses any fixed target. -/

namespace LowRank
open Matrix MeasureTheory ProbabilityTheory
open scoped Matrix BigOperators
noncomputable section

theorem iidVectorLaw_dot_ne_ae {r : ℕ} {v : NNReal} (hv : v ≠ 0)
    (u : Fin r → ℝ) (hu : u ≠ 0) (c : ℝ) :
    ∀ᵐ x ∂iidVectorLaw r v, u ⬝ᵥ x ≠ c := by
  cases r with
  | zero => exact (hu (Subsingleton.elim _ _)).elim
  | succ r =>
    let b := EuclideanSpace.basisFun (Fin (r + 1)) ℝ
    let ρ := ‖(basisCoordinates b).symm u‖
    have hρ : ρ ≠ 0 := by
      apply norm_ne_zero_iff.mpr
      intro h
      apply hu
      have heq := congrArg (basisCoordinates b) h
      simpa only [ContinuousLinearEquiv.apply_symm_apply, map_zero] using heq
    have hcoord : ∀ᵐ x ∂iidVectorLaw (r + 1) v, x 0 ≠ c / ρ := by
      apply ae_iff.mpr
      simpa only [not_not, iidVectorLaw, Set.preimage, Set.mem_singleton_iff, Function.eval] using
        Measure.pi_eval_preimage_null (fun _ : Fin (r + 1) => gaussianReal 0 v)
          (i := 0) ((gaussianReal_absolutelyContinuous 0 hv) (measure_singleton (c / ρ)))
    let U := coordinateRotation b (rowGauge b u)
    have hpres : MeasurePreserving U (iidVectorLaw (r + 1) v) (iidVectorLaw (r + 1) v) :=
      ⟨U.continuous.measurable, iidVectorLaw_coordinateRotation b (rowGauge b u) v⟩
    filter_upwards [hpres.quasiMeasurePreserving.ae hcoord] with x hx
    intro heq
    apply hx
    apply (eq_div_iff hρ).mpr
    have hdot := coordinateRotation_dot b (rowGauge b u) u x
    simp_rw [rowGauge_aligns] at hdot
    have hvalue : ρ * U x 0 = u ⬝ᵥ x := by simpa [dotProduct, ρ, U] using hdot
    rw [mul_comm, hvalue, heq]

theorem iidMatrixLaw_mul_ne_ae {a r s : ℕ} (hs : 0 < s) {v : NNReal} (hv : v ≠ 0)
    (M : Matrix (Fin a) (Fin r) ℝ) (hM : M ≠ 0)
    (N : Matrix (Fin a) (Fin s) ℝ) :
    ∀ᵐ D ∂iidMatrixLaw r s v, M * D ≠ N := by
  classical
  obtain ⟨i, j, hij⟩ : ∃ i j, M i j ≠ 0 := by
    by_contra! h
    apply hM
    ext i j
    exact h i j
  have hi : M i ≠ 0 := fun h => hij (congrFun h j)
  cases s with
  | zero => omega
  | succ s =>
    have hdot := iidVectorLaw_dot_ne_ae hv (M i) hi (N i 0)
    have hprod : ∀ᵐ x ∂(iidVectorLaw r v).prod (iidMatrixLaw r s v), M i ⬝ᵥ x.1 ≠ N i 0 :=
      Measure.quasiMeasurePreserving_fst.ae hdot
    filter_upwards [(splitFirstColumn_preserving r s v).quasiMeasurePreserving.ae hprod] with D hD
    intro heq
    exact hD (congrFun (congrFun heq i) 0)

theorem iidMatrixLaw_affine_ne_zero_ae {a r s : ℕ} (hs : 0 < s) {v : NNReal} (hv : v ≠ 0)
    (M : Matrix (Fin a) (Fin r) ℝ) (hM : M ≠ 0)
    (N : Matrix (Fin a) (Fin s) ℝ) :
    ∀ᵐ D ∂iidMatrixLaw r s v, N + M * D ≠ 0 := by
  filter_upwards [iidMatrixLaw_mul_ne_ae hs hv M hM (-N)] with D hD
  intro hzero
  apply hD
  exact eq_neg_of_add_eq_zero_right hzero

end
end LowRank
