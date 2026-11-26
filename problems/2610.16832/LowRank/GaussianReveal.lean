import LowRank.MeasurableHouseholder

/-! One actual Gaussian block revelation. The exposed state keeps the entire
latent first row, a stronger invariant than keeping only the oracle reply. -/

namespace LowRank
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {r s : ℕ}

def rowGauge (b : OrthonormalBasis (Fin (s + 1)) ℝ E) (z : Fin (s + 1) → ℝ) :
    E ≃ₗᵢ[ℝ] E := alignToAxis (b 0) ((basisCoordinates b).symm z)

theorem rowGauge_aligns (b : OrthonormalBasis (Fin (s + 1)) ℝ E)
    (z : Fin (s + 1) → ℝ) (j : Fin (s + 1)) :
    coordinateRotation b (rowGauge b z) z j =
      if j = 0 then ‖(basisCoordinates b).symm z‖ else 0 := by
  change b.repr (alignToAxis (b 0) ((basisCoordinates b).symm z)
    ((basisCoordinates b).symm z)) j = _
  rw [alignToAxis_self (b.norm_eq_one 0), b.repr_apply_apply, inner_smul_right,
    orthonormal_iff_ite.mp b.orthonormal]
  split_ifs <;> simp_all

theorem rowGauge_pivot_positive_ae (b : OrthonormalBasis (Fin (s + 1)) ℝ E)
    {v : NNReal} (hv : v ≠ 0) :
    ∀ᵐ z ∂iidVectorLaw (s + 1) v, 0 < ‖(basisCoordinates b).symm z‖ := by
  have hcoord : ∀ᵐ z ∂iidVectorLaw (s + 1) v, z 0 ≠ 0 := by
    apply ae_iff.mpr
    simpa only [not_not, iidVectorLaw, Set.preimage, Set.mem_singleton_iff, Function.eval] using
      Measure.pi_eval_preimage_null (fun _ : Fin (s + 1) => gaussianReal 0 v)
        (i := 0) ((gaussianReal_absolutelyContinuous 0 hv) (measure_singleton 0))
  filter_upwards [hcoord] with z hz
  apply norm_pos_iff.mpr
  intro hzero
  have heq : z = 0 := by
    have h := congrArg (basisCoordinates b) hzero
    simpa using h
  exact hz (congrFun heq 0)

theorem measurable_rowGauge_rotation (b : OrthonormalBasis (Fin (s + 1)) ℝ E) :
    Measurable (fun p : (Fin (s + 1) → ℝ) × Matrix (Fin r) (Fin (s + 1)) ℝ =>
      rotateMatrixRows b (rowGauge b p.1) p.2) := by
  apply measurable_pi_lambda
  intro i
  simp only [rotateMatrixRows_apply, rowGauge, alignToAxis, householder_apply]
  apply (basisCoordinates b).continuous.measurable.comp
  fun_prop

def revealGaussianBlock (b : OrthonormalBasis (Fin (s + 1)) ℝ E)
    (X : Matrix (Fin (r + 1)) (Fin (s + 1)) ℝ) :
    ((Fin (s + 1) → ℝ) × (Fin r → ℝ)) × Matrix (Fin r) (Fin s) ℝ :=
  let z := X 0
  let Y := rotateMatrixRows b (rowGauge b z) (fun i => X i.succ)
  ((z, fun i => Y i 0), fun i j => Y i j.succ)

/-- The unexposed block is iid Gaussian and independent of both the latent
first row and the newly exposed column. No conditional-Gaussian premise is used. -/
theorem revealGaussianBlock_preserving (b : OrthonormalBasis (Fin (s + 1)) ℝ E)
    (v : NNReal) :
    MeasurePreserving (revealGaussianBlock (r := r) b) (iidMatrixLaw (r + 1) (s + 1) v)
      (((iidVectorLaw (s + 1) v).prod (iidVectorLaw r v)).prod (iidMatrixLaw r s v)) := by
  letI : IsProbabilityMeasure (iidVectorLaw (s + 1) v) := iidVectorLaw_probability _ _
  letI : IsProbabilityMeasure (iidVectorLaw r v) := iidVectorLaw_probability _ _
  letI : IsProbabilityMeasure (iidMatrixLaw r s v) := iidMatrixLaw_probability _ _ _
  letI : IsProbabilityMeasure (iidMatrixLaw r (s + 1) v) := iidMatrixLaw_probability _ _ _
  have hrow := splitFirstRow_preserving r (s + 1) v
  have hrot : MeasurePreserving
      (fun p : (Fin (s + 1) → ℝ) × Matrix (Fin r) (Fin (s + 1)) ℝ =>
        (p.1, rotateMatrixRows b (rowGauge b p.1) p.2))
      ((iidVectorLaw (s + 1) v).prod (iidMatrixLaw r (s + 1) v))
      ((iidVectorLaw (s + 1) v).prod (iidMatrixLaw r (s + 1) v)) :=
    ⟨measurable_fst.prodMk (measurable_rowGauge_rotation b),
      state_dependent_matrix_rotation b (rowGauge b) v (measurable_rowGauge_rotation b)⟩
  have hcol : MeasurePreserving
      (fun p : (Fin (s + 1) → ℝ) × Matrix (Fin r) (Fin (s + 1)) ℝ =>
        (p.1, splitFirstColumn p.2))
      ((iidVectorLaw (s + 1) v).prod (iidMatrixLaw r (s + 1) v))
      ((iidVectorLaw (s + 1) v).prod ((iidVectorLaw r v).prod (iidMatrixLaw r s v))) :=
    (MeasurePreserving.id (iidVectorLaw (s + 1) v)).prod (splitFirstColumn_preserving r s v)
  have hassoc := (measurePreserving_prodAssoc (iidVectorLaw (s + 1) v)
    (iidVectorLaw r v) (iidMatrixLaw r s v)).symm MeasurableEquiv.prodAssoc
  exact hassoc.comp (hcol.comp (hrot.comp hrow))

theorem revealGaussianBlock_residual_law (b : OrthonormalBasis (Fin (s + 1)) ℝ E)
    (v : NNReal) :
    (iidMatrixLaw (r + 1) (s + 1) v).map (fun X => (revealGaussianBlock b X).2) =
      iidMatrixLaw r s v := by
  have h := revealGaussianBlock_preserving (r := r) b v
  calc
    _ = ((iidMatrixLaw (r + 1) (s + 1) v).map (revealGaussianBlock b)).map Prod.snd :=
      (Measure.map_map measurable_snd h.measurable).symm
    _ = _ := by rw [h.map_eq]; simp

theorem revealGaussianBlock_independent (b : OrthonormalBasis (Fin (s + 1)) ℝ E)
    (v : NNReal) :
    IndepFun (fun X => (revealGaussianBlock (r := r) b X).1)
      (fun X => (revealGaussianBlock b X).2) (iidMatrixLaw (r + 1) (s + 1) v) := by
  have h := revealGaussianBlock_preserving (r := r) b v
  rw [indepFun_iff_map_prod_eq_prod_map_map h.measurable.fst.aemeasurable
    h.measurable.snd.aemeasurable]
  change (iidMatrixLaw (r + 1) (s + 1) v).map (revealGaussianBlock b) = _
  rw [h.map_eq, revealGaussianBlock_residual_law]
  congr 1
  symm
  calc
    _ = ((iidMatrixLaw (r + 1) (s + 1) v).map (revealGaussianBlock b)).map Prod.fst :=
      (Measure.map_map measurable_fst h.measurable).symm
    _ = _ := by rw [h.map_eq]; simp

/-- A prior independent state can be retained in the enlarged exposed state. -/
theorem revealGaussianBlock_with_state {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [SFinite ν] (b : OrthonormalBasis (Fin (s + 1)) ℝ E) (v : NNReal) :
    MeasurePreserving
      (fun p : S × Matrix (Fin (r + 1)) (Fin (s + 1)) ℝ =>
        ((p.1, (revealGaussianBlock b p.2).1), (revealGaussianBlock b p.2).2))
      (ν.prod (iidMatrixLaw (r + 1) (s + 1) v))
      ((ν.prod ((iidVectorLaw (s + 1) v).prod (iidVectorLaw r v))).prod
        (iidMatrixLaw r s v)) := by
  letI : IsProbabilityMeasure (iidVectorLaw (s + 1) v) := iidVectorLaw_probability _ _
  letI : IsProbabilityMeasure (iidVectorLaw r v) := iidVectorLaw_probability _ _
  letI : IsProbabilityMeasure ((iidVectorLaw (s + 1) v).prod (iidVectorLaw r v)) :=
    Measure.prod.instIsProbabilityMeasure _ _
  letI : IsProbabilityMeasure (iidMatrixLaw r s v) := iidMatrixLaw_probability _ _ _
  letI : SFinite (iidVectorLaw (s + 1) v) := by infer_instance
  letI : SFinite (iidVectorLaw r v) := by infer_instance
  letI : SFinite ((iidVectorLaw (s + 1) v).prod (iidVectorLaw r v)) :=
    Measure.prod.instSFinite
  letI : SFinite (iidMatrixLaw r s v) := by infer_instance
  have hprod : MeasurePreserving
      (fun p : S × Matrix (Fin (r + 1)) (Fin (s + 1)) ℝ =>
        (p.1, revealGaussianBlock b p.2))
      (ν.prod (iidMatrixLaw (r + 1) (s + 1) v))
      (ν.prod (((iidVectorLaw (s + 1) v).prod (iidVectorLaw r v)).prod
        (iidMatrixLaw r s v))) :=
    (MeasurePreserving.id ν).prod (revealGaussianBlock_preserving b v)
  have hassoc := measurePreserving_prodAssoc ν
    ((iidVectorLaw (s + 1) v).prod (iidVectorLaw r v)) (iidMatrixLaw r s v)
  have hinv := hassoc.symm MeasurableEquiv.prodAssoc
  exact hinv.comp hprod

end
end LowRank
