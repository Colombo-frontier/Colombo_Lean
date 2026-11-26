import LowRank.GaussianGaugeMatrix
import LowRank.GaussianMatrixCompression
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Tactic

/-!
# A direct two-sided Gaussian revelation step

Both coordinate rotations below are chosen from the previous state, before
either reply is exposed. We reveal the first row and the remaining entries of
the first column. The resulting lower-right block is genuinely independent iid
Gaussian. This is not the response-aligned Gram-oracle revelation.

The module proves one step from an independent Gaussian block, not the complete
adaptive posterior theorem for arbitrary ambient transcripts.
-/

namespace Matvec
open Matrix MeasureTheory ProbabilityTheory
open scoped Matrix BigOperators
noncomputable section

variable {r s : ℕ}

/-- Reveal a first row and first column, counting their shared entry only once. -/
def splitTwoSided (X : Matrix (Fin (r + 1)) (Fin (s + 1)) ℝ) :
    ((Fin (s + 1) → ℝ) × (Fin r → ℝ)) × Matrix (Fin r) (Fin s) ℝ :=
  ((X 0, fun i => X i.succ 0), fun i j => X i.succ j.succ)

theorem splitTwoSided_preserving (r s : ℕ) (v : NNReal) :
    MeasurePreserving (splitTwoSided (r := r) (s := s))
      (LowRank.iidMatrixLaw (r + 1) (s + 1) v)
      (((LowRank.iidVectorLaw (s + 1) v).prod (LowRank.iidVectorLaw r v)).prod
        (LowRank.iidMatrixLaw r s v)) := by
  letI : IsProbabilityMeasure (LowRank.iidVectorLaw (s + 1) v) := LowRank.iidVectorLaw_probability _ _
  letI : IsProbabilityMeasure (LowRank.iidVectorLaw r v) := LowRank.iidVectorLaw_probability _ _
  letI : IsProbabilityMeasure (LowRank.iidMatrixLaw r s v) := LowRank.iidMatrixLaw_probability _ _ _
  letI : SFinite (LowRank.iidVectorLaw (s + 1) v) := by infer_instance
  letI : SFinite (LowRank.iidVectorLaw r v) := by infer_instance
  letI : SFinite (LowRank.iidMatrixLaw r s v) := by infer_instance
  have hrow := LowRank.splitFirstRow_preserving r (s + 1) v
  have hcol := (MeasurePreserving.id (LowRank.iidVectorLaw (s + 1) v)).prod
    (LowRank.splitFirstColumn_preserving r s v)
  have ha := (measurePreserving_prodAssoc (LowRank.iidVectorLaw (s + 1) v)
    (LowRank.iidVectorLaw r v) (LowRank.iidMatrixLaw r s v)).symm MeasurableEquiv.prodAssoc
  exact ha.comp (hcol.comp hrow)

theorem splitTwoSided_with_state {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [SFinite ν] (r s : ℕ) (v : NNReal) :
    MeasurePreserving
      (fun p : S × Matrix (Fin (r + 1)) (Fin (s + 1)) ℝ =>
        ((p.1, (splitTwoSided p.2).1), (splitTwoSided p.2).2))
      (ν.prod (LowRank.iidMatrixLaw (r + 1) (s + 1) v))
      ((ν.prod ((LowRank.iidVectorLaw (s + 1) v).prod (LowRank.iidVectorLaw r v))).prod
        (LowRank.iidMatrixLaw r s v)) := by
  letI : IsProbabilityMeasure (LowRank.iidVectorLaw (s + 1) v) := LowRank.iidVectorLaw_probability _ _
  letI : IsProbabilityMeasure (LowRank.iidVectorLaw r v) := LowRank.iidVectorLaw_probability _ _
  letI : IsProbabilityMeasure ((LowRank.iidVectorLaw (s + 1) v).prod
      (LowRank.iidVectorLaw r v)) := Measure.prod.instIsProbabilityMeasure _ _
  letI : IsProbabilityMeasure (LowRank.iidMatrixLaw r s v) := LowRank.iidMatrixLaw_probability _ _ _
  letI : SFinite (LowRank.iidVectorLaw (s + 1) v) := by infer_instance
  letI : SFinite (LowRank.iidVectorLaw r v) := by infer_instance
  letI : SFinite ((LowRank.iidVectorLaw (s + 1) v).prod (LowRank.iidVectorLaw r v)) :=
    Measure.prod.instSFinite
  letI : SFinite (LowRank.iidMatrixLaw r s v) := by infer_instance
  have hp := (MeasurePreserving.id ν).prod (splitTwoSided_preserving r s v)
  have ha := (measurePreserving_prodAssoc ν
    ((LowRank.iidVectorLaw (s + 1) v).prod (LowRank.iidVectorLaw r v))
    (LowRank.iidMatrixLaw r s v)).symm MeasurableEquiv.prodAssoc
  exact ha.comp hp

/-- Coordinate rotations on the left and right of the same matrix. -/
def twoSidedRotate (L : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ)
    (R : Matrix (Fin (s + 1)) (Fin (s + 1)) ℝ)
    (X : Matrix (Fin (r + 1)) (Fin (s + 1)) ℝ) := L * X * Rᵀ

theorem twoSidedRotate_preserving
    (L : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ)
    (R : Matrix (Fin (s + 1)) (Fin (s + 1)) ℝ)
    (hL : L * Lᵀ = 1) (hR : R * Rᵀ = 1) (v : NNReal) :
    MeasurePreserving (twoSidedRotate L R)
      (LowRank.iidMatrixLaw (r + 1) (s + 1) v)
      (LowRank.iidMatrixLaw (r + 1) (s + 1) v) := by
  have hl := LowRank.iidMatrixLaw_left_compression_preserving
    (r := s + 1) Lᵀ (by simpa using hL) v
  have hr : MeasurePreserving
      (fun X : Matrix (Fin (r + 1)) (Fin (s + 1)) ℝ => X * Rᵀ)
      (LowRank.iidMatrixLaw (r + 1) (s + 1) v)
      (LowRank.iidMatrixLaw (r + 1) (s + 1) v) :=
    ⟨(by fun_prop : Continuous _).measurable,
      LowRank.iidMatrixLaw_right_compression Rᵀ (by simpa using hR) v⟩
  simpa only [twoSidedRotate, Function.comp_def, Matrix.transpose_transpose] using hr.comp hl

section State
variable {S : Type*} [MeasurableSpace S]

theorem measurable_twoSidedRotate
    (L : S → Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ)
    (R : S → Matrix (Fin (s + 1)) (Fin (s + 1)) ℝ)
    (hL : Measurable L) (hR : Measurable R) :
    Measurable (fun p : S × Matrix (Fin (r + 1)) (Fin (s + 1)) ℝ =>
      twoSidedRotate (L p.1) (R p.1) p.2) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  simp only [twoSidedRotate, Matrix.mul_apply, Matrix.transpose_apply]
  fun_prop

def twoSidedGaussianStep
    (L : S → Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ)
    (R : S → Matrix (Fin (s + 1)) (Fin (s + 1)) ℝ)
    (p : S × Matrix (Fin (r + 1)) (Fin (s + 1)) ℝ) :
    (S × ((Fin (s + 1) → ℝ) × (Fin r → ℝ))) × Matrix (Fin r) (Fin s) ℝ :=
  let out := splitTwoSided (twoSidedRotate (L p.1) (R p.1) p.2)
  ((p.1, out.1), out.2)

/-- A genuine two-sided, state-adaptive step. Its exact product law is proved
from Gaussian invariance and coordinate product decomposition. -/
theorem twoSidedGaussianStep_preserving (ν : Measure S) [SFinite ν]
    (L : S → Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ)
    (R : S → Matrix (Fin (s + 1)) (Fin (s + 1)) ℝ)
    (hL : Measurable L) (hR : Measurable R)
    (horthL : ∀ z, L z * (L z)ᵀ = 1) (horthR : ∀ z, R z * (R z)ᵀ = 1)
    (v : NNReal) :
    MeasurePreserving (twoSidedGaussianStep L R)
      (ν.prod (LowRank.iidMatrixLaw (r + 1) (s + 1) v))
      ((ν.prod ((LowRank.iidVectorLaw (s + 1) v).prod (LowRank.iidVectorLaw r v))).prod
        (LowRank.iidMatrixLaw r s v)) := by
  have hrot := (MeasurePreserving.id ν).skew_product (measurable_twoSidedRotate L R hL hR)
    (Filter.Eventually.of_forall (fun z => (twoSidedRotate_preserving
      (L z) (R z) (horthL z) (horthR z) v).map_eq))
  exact (splitTwoSided_with_state ν r s v).comp hrot

theorem twoSidedGaussianStep_residual_law (ν : Measure S) [IsProbabilityMeasure ν]
    (L : S → Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ)
    (R : S → Matrix (Fin (s + 1)) (Fin (s + 1)) ℝ)
    (hL : Measurable L) (hR : Measurable R)
    (horthL : ∀ z, L z * (L z)ᵀ = 1) (horthR : ∀ z, R z * (R z)ᵀ = 1)
    (v : NNReal) :
    (ν.prod (LowRank.iidMatrixLaw (r + 1) (s + 1) v)).map
      (fun p => (twoSidedGaussianStep L R p).2) = LowRank.iidMatrixLaw r s v := by
  have hp := twoSidedGaussianStep_preserving ν L R hL hR horthL horthR v
  calc
    _ = ((ν.prod (LowRank.iidMatrixLaw (r + 1) (s + 1) v)).map
        (twoSidedGaussianStep L R)).map Prod.snd :=
      (Measure.map_map measurable_snd hp.measurable).symm
    _ = _ := by rw [hp.map_eq]; simp

theorem twoSidedGaussianStep_independent (ν : Measure S) [IsProbabilityMeasure ν]
    (L : S → Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ)
    (R : S → Matrix (Fin (s + 1)) (Fin (s + 1)) ℝ)
    (hL : Measurable L) (hR : Measurable R)
    (horthL : ∀ z, L z * (L z)ᵀ = 1) (horthR : ∀ z, R z * (R z)ᵀ = 1)
    (v : NNReal) :
    IndepFun (fun p => (twoSidedGaussianStep L R p).1)
      (fun p => (twoSidedGaussianStep L R p).2)
      (ν.prod (LowRank.iidMatrixLaw (r + 1) (s + 1) v)) := by
  have hp := twoSidedGaussianStep_preserving ν L R hL hR horthL horthR v
  rw [indepFun_iff_map_prod_eq_prod_map_map hp.measurable.fst.aemeasurable
    hp.measurable.snd.aemeasurable]
  change (ν.prod (LowRank.iidMatrixLaw (r + 1) (s + 1) v)).map (twoSidedGaussianStep L R) = _
  rw [hp.map_eq, twoSidedGaussianStep_residual_law ν L R hL hR horthL horthR]
  congr 1
  symm
  calc
    _ = ((ν.prod (LowRank.iidMatrixLaw (r + 1) (s + 1) v)).map
        (twoSidedGaussianStep L R)).map Prod.fst :=
      (Measure.map_map measurable_fst hp.measurable).symm
    _ = _ := by rw [hp.map_eq]; simp

theorem twoSidedGaussianStep_conditional_bounded (ν : Measure S) [IsProbabilityMeasure ν]
    (L : S → Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ)
    (R : S → Matrix (Fin (s + 1)) (Fin (s + 1)) ℝ)
    (hL : Measurable L) (hR : Measurable R)
    (horthL : ∀ z, L z * (L z)ᵀ = 1) (horthR : ∀ z, R z * (R z)ᵀ = 1)
    (v : NNReal) (φ : Matrix (Fin r) (Fin s) ℝ → ℝ) (hφ : Measurable φ)
    (C : ℝ) (hbound : ∀ D, ‖φ D‖ ≤ C) :
    let μ := ν.prod (LowRank.iidMatrixLaw (r + 1) (s + 1) v)
    let T := fun p => (twoSidedGaussianStep L R p).1
    let Z := fun p => (twoSidedGaussianStep L R p).2
    Integrable (φ ∘ Z) μ ∧
      μ[φ ∘ Z | MeasurableSpace.comap T inferInstance] =ᵐ[μ]
        (fun _ => ∫ D, φ D ∂LowRank.iidMatrixLaw r s v) := by
  let μ := ν.prod (LowRank.iidMatrixLaw (r + 1) (s + 1) v)
  let T := fun p => (twoSidedGaussianStep L R p).1
  let Z := fun p => (twoSidedGaussianStep L R p).2
  have hp := twoSidedGaussianStep_preserving ν L R hL hR horthL horthR v
  have hT : Measurable T := hp.measurable.fst
  have hZ : Measurable Z := hp.measurable.snd
  have hZlaw : MeasurePreserving Z μ (LowRank.iidMatrixLaw r s v) :=
    ⟨hZ, twoSidedGaussianStep_residual_law ν L R hL hR horthL horthR v⟩
  have hφint : Integrable φ (LowRank.iidMatrixLaw r s v) :=
    (integrable_const C).mono' hφ.stronglyMeasurable.aestronglyMeasurable
      (Filter.Eventually.of_forall hbound)
  refine ⟨(hZlaw.integrable_comp hφ.stronglyMeasurable.aestronglyMeasurable).mpr hφint, ?_⟩
  have hind : IndepFun Z T μ :=
    (twoSidedGaussianStep_independent ν L R hL hR horthL horthR v).symm
  have hsm : StronglyMeasurable[(inferInstance : MeasurableSpace (Matrix (Fin r) (Fin s) ℝ)).comap Z]
      (φ ∘ Z) := (hφ.comp (comap_measurable Z)).stronglyMeasurable
  have hc := condExp_indep_eq hZ.comap_le hT.comap_le hsm ((IndepFun_iff_Indep Z T μ).mp hind)
  have hi : (∫ p, φ (Z p) ∂μ) = ∫ D, φ D ∂LowRank.iidMatrixLaw r s v := by
    rw [← hZlaw.map_eq, integral_map_of_stronglyMeasurable hZ hφ.stronglyMeasurable]
  simpa only [Function.comp_def, hi] using hc

end State

section Queries

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]

/-- An explicit measurable orthogonal rotation selected from a query vector. -/
def queryGauge (b : OrthonormalBasis (Fin (r + 1)) ℝ E) (u : Fin (r + 1) → ℝ) :=
  LowRank.gaugeMatrix b (LowRank.rowGauge b u)

theorem measurable_queryGauge (b : OrthonormalBasis (Fin (r + 1)) ℝ E) :
    Measurable (queryGauge b) := LowRank.measurable_rowGauge_matrix b

theorem queryGauge_orthogonal (b : OrthonormalBasis (Fin (r + 1)) ℝ E)
    (u : Fin (r + 1) → ℝ) : queryGauge b u * (queryGauge b u)ᵀ = 1 :=
  LowRank.gaugeMatrix_mul_transpose_self b (LowRank.rowGauge b u)

/-- Both query rotations depend on the prior state, and can be selected from
arbitrary measurable real query vectors (including zero vectors). -/
theorem queryGaussianStep_preserving {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [SFinite ν]
    (b : OrthonormalBasis (Fin (r + 1)) ℝ E)
    (c : OrthonormalBasis (Fin (s + 1)) ℝ F)
    (u : S → Fin (r + 1) → ℝ) (w : S → Fin (s + 1) → ℝ)
    (hu : Measurable u) (hw : Measurable w) (v : NNReal) :
    MeasurePreserving
      (twoSidedGaussianStep (fun z => queryGauge b (u z)) (fun z => queryGauge c (w z)))
      (ν.prod (LowRank.iidMatrixLaw (r + 1) (s + 1) v))
      ((ν.prod ((LowRank.iidVectorLaw (s + 1) v).prod (LowRank.iidVectorLaw r v))).prod
        (LowRank.iidMatrixLaw r s v)) :=
  twoSidedGaussianStep_preserving ν _ _ ((measurable_queryGauge b).comp hu)
    ((measurable_queryGauge c).comp hw)
    (fun z => queryGauge_orthogonal b (u z)) (fun z => queryGauge_orthogonal c (w z)) v

theorem twoSided_query_rotation_eq
    (b : OrthonormalBasis (Fin (r + 1)) ℝ E)
    (c : OrthonormalBasis (Fin (s + 1)) ℝ F)
    (u : Fin (r + 1) → ℝ) (w : Fin (s + 1) → ℝ)
    (X : Matrix (Fin (r + 1)) (Fin (s + 1)) ℝ) :
    twoSidedRotate (queryGauge b u) (queryGauge c w) X =
      LowRank.rotateMatrixRows c (LowRank.rowGauge c w)
        (LowRank.rotateMatrixColumns b (LowRank.rowGauge b u) X) := by
  rw [LowRank.rotateMatrixRows_eq_mul, LowRank.rotateMatrixColumns_eq_mul]
  rfl

/-- The exposed row is precisely the left oracle reply in the known right basis. -/
theorem twoSided_query_first_row
    (b : OrthonormalBasis (Fin (r + 1)) ℝ E)
    (c : OrthonormalBasis (Fin (s + 1)) ℝ F)
    (u : Fin (r + 1) → ℝ) (w : Fin (s + 1) → ℝ)
    (hu : ‖(LowRank.basisCoordinates b).symm u‖ = 1)
    (X : Matrix (Fin (r + 1)) (Fin (s + 1)) ℝ) :
    twoSidedRotate (queryGauge b u) (queryGauge c w) X 0 =
      LowRank.coordinateRotation c (LowRank.rowGauge c w) (Xᵀ *ᵥ u) := by
  rw [twoSided_query_rotation_eq]
  change LowRank.coordinateRotation c (LowRank.rowGauge c w)
    (LowRank.rotateMatrixColumns b (LowRank.rowGauge b u) X 0) = _
  rw [LowRank.query_rotation_first_row b u hu X]

/-- The exposed column is precisely the right oracle reply in the known left basis. -/
theorem twoSided_query_first_column
    (b : OrthonormalBasis (Fin (r + 1)) ℝ E)
    (c : OrthonormalBasis (Fin (s + 1)) ℝ F)
    (u : Fin (r + 1) → ℝ) (w : Fin (s + 1) → ℝ)
    (hw : ‖(LowRank.basisCoordinates c).symm w‖ = 1)
    (X : Matrix (Fin (r + 1)) (Fin (s + 1)) ℝ) :
    (fun i => twoSidedRotate (queryGauge b u) (queryGauge c w) X i 0) =
      LowRank.coordinateRotation b (LowRank.rowGauge b u) (X *ᵥ w) := by
  funext i
  rw [twoSided_query_rotation_eq]
  change LowRank.coordinateRotation c (LowRank.rowGauge c w)
    (LowRank.rotateMatrixColumns b (LowRank.rowGauge b u) X i) 0 = _
  rw [LowRank.query_rotation_first_coordinate c w _ hw]
  have h := congrFun (LowRank.rotateMatrixColumns_mulVec b (LowRank.rowGauge b u) X w) i
  simpa only [Matrix.mulVec, dotProduct, mul_comm] using h

/-- Reassemble the first column from the row-column record and undo both known
rotations. Thus the record contains the actual two-sided oracle answer. -/
def exposedTwoSidedReply
    (b : OrthonormalBasis (Fin (r + 1)) ℝ E)
    (c : OrthonormalBasis (Fin (s + 1)) ℝ F)
    (u : Fin (r + 1) → ℝ) (w : Fin (s + 1) → ℝ)
    (record : (Fin (s + 1) → ℝ) × (Fin r → ℝ)) :
    (Fin (r + 1) → ℝ) × (Fin (s + 1) → ℝ) :=
  (LowRank.coordinateRotation b (LowRank.rowGauge b u) (Fin.cons (record.1 0) record.2),
    LowRank.coordinateRotation c (LowRank.rowGauge c w) record.1)

theorem exposedTwoSidedReply_eq_oracle
    (b : OrthonormalBasis (Fin (r + 1)) ℝ E)
    (c : OrthonormalBasis (Fin (s + 1)) ℝ F)
    (u : Fin (r + 1) → ℝ) (w : Fin (s + 1) → ℝ)
    (hu : ‖(LowRank.basisCoordinates b).symm u‖ = 1)
    (hw : ‖(LowRank.basisCoordinates c).symm w‖ = 1)
    (X : Matrix (Fin (r + 1)) (Fin (s + 1)) ℝ) :
    exposedTwoSidedReply b c u w
      (splitTwoSided (twoSidedRotate (queryGauge b u) (queryGauge c w) X)).1 =
      (X *ᵥ w, Xᵀ *ᵥ u) := by
  let Z := twoSidedRotate (queryGauge b u) (queryGauge c w) X
  have hcol : Fin.cons (Z 0 0) (fun i => Z i.succ 0) = fun i => Z i 0 := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  apply Prod.ext
  · change LowRank.coordinateRotation b (LowRank.rowGauge b u)
      (Fin.cons (Z 0 0) (fun i => Z i.succ 0)) = _
    rw [hcol, twoSided_query_first_column b c u w hw X]
    exact LowRank.query_rotation_involutive b u _
  · change LowRank.coordinateRotation c (LowRank.rowGauge c w)
      (twoSidedRotate (queryGauge b u) (queryGauge c w) X 0) = _
    rw [twoSided_query_first_row b c u w hu X]
    exact LowRank.query_rotation_involutive c w _

theorem measurable_queryGauge_eval (b : OrthonormalBasis (Fin (r + 1)) ℝ E) :
    Measurable (fun p : (Fin (r + 1) → ℝ) × (Fin (r + 1) → ℝ) =>
      LowRank.coordinateRotation b (LowRank.rowGauge b p.1) p.2) := by
  simp only [LowRank.coordinateRotation_apply, LowRank.rowGauge,
    LowRank.alignToAxis, LowRank.householder_apply]
  fun_prop

theorem measurable_exposedTwoSidedReply {S : Type*} [MeasurableSpace S]
    (b : OrthonormalBasis (Fin (r + 1)) ℝ E)
    (c : OrthonormalBasis (Fin (s + 1)) ℝ F)
    (u : S → Fin (r + 1) → ℝ) (w : S → Fin (s + 1) → ℝ)
    (hu : Measurable u) (hw : Measurable w) :
    Measurable (fun p : S × ((Fin (s + 1) → ℝ) × (Fin r → ℝ)) =>
      (p.1, exposedTwoSidedReply b c (u p.1) (w p.1) p.2)) := by
  have hcol : Measurable (fun p : S × ((Fin (s + 1) → ℝ) × (Fin r → ℝ)) =>
      (Fin.cons (p.2.1 0) p.2.2 : Fin (r + 1) → ℝ)) := by
    apply measurable_pi_lambda
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (measurable_pi_apply (0 : Fin (s + 1))).comp measurable_snd.fst
    · exact (measurable_pi_apply j).comp measurable_snd.snd
  have hmatL : Measurable (fun p : S × ((Fin (s + 1) → ℝ) × (Fin r → ℝ)) =>
      queryGauge b (u p.1)) := (measurable_queryGauge b).comp (hu.comp measurable_fst)
  have hmatR : Measurable (fun p : S × ((Fin (s + 1) → ℝ) × (Fin r → ℝ)) =>
      queryGauge c (w p.1)) := (measurable_queryGauge c).comp (hw.comp measurable_fst)
  have hleft : Measurable (fun p : S × ((Fin (s + 1) → ℝ) × (Fin r → ℝ)) =>
      queryGauge b (u p.1) *ᵥ (Fin.cons (p.2.1 0) p.2.2 : Fin (r + 1) → ℝ)) := by
    apply measurable_pi_lambda
    intro i
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.measurable_sum _ (fun j _ =>
      (((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hmatL)).mul
        ((measurable_pi_apply j).comp hcol)))
  have hright : Measurable (fun p : S × ((Fin (s + 1) → ℝ) × (Fin r → ℝ)) =>
      queryGauge c (w p.1) *ᵥ p.2.1) := by
    apply measurable_pi_lambda
    intro i
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.measurable_sum _ (fun j _ =>
      (((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hmatR)).mul
        ((measurable_pi_apply j).comp measurable_snd.fst)))
  simpa only [queryGauge, LowRank.gaugeMatrix_mulVec, exposedTwoSidedReply] using
    (measurable_fst.prodMk (hleft.prodMk hright))

/-- For unit left and right queries, the independent Gaussian residual is
independent of the actual prior-state-plus-two-sided-oracle-reply record. -/
theorem twoSidedQuery_reply_residual_independent {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν]
    (b : OrthonormalBasis (Fin (r + 1)) ℝ E)
    (c : OrthonormalBasis (Fin (s + 1)) ℝ F)
    (u : S → Fin (r + 1) → ℝ) (w : S → Fin (s + 1) → ℝ)
    (hu : Measurable u) (hw : Measurable w)
    (hunitU : ∀ z, ‖(LowRank.basisCoordinates b).symm (u z)‖ = 1)
    (hunitW : ∀ z, ‖(LowRank.basisCoordinates c).symm (w z)‖ = 1)
    (v : NNReal) :
    IndepFun
      (fun p : S × Matrix (Fin (r + 1)) (Fin (s + 1)) ℝ =>
        (p.1, (p.2 *ᵥ w p.1, p.2ᵀ *ᵥ u p.1)))
      (fun p => (twoSidedGaussianStep
        (fun z => queryGauge b (u z)) (fun z => queryGauge c (w z)) p).2)
      (ν.prod (LowRank.iidMatrixLaw (r + 1) (s + 1) v)) := by
  have hi := twoSidedGaussianStep_independent ν
    (fun z => queryGauge b (u z)) (fun z => queryGauge c (w z))
    ((measurable_queryGauge b).comp hu) ((measurable_queryGauge c).comp hw)
    (fun z => queryGauge_orthogonal b (u z)) (fun z => queryGauge_orthogonal c (w z)) v
  let recover := fun p : S × ((Fin (s + 1) → ℝ) × (Fin r → ℝ)) =>
    (p.1, exposedTwoSidedReply b c (u p.1) (w p.1) p.2)
  have hm : Measurable recover := measurable_exposedTwoSidedReply b c u w hu hw
  have hind := hi.comp hm measurable_id
  have heq : recover ∘ (fun p => (twoSidedGaussianStep
      (fun z => queryGauge b (u z)) (fun z => queryGauge c (w z)) p).1) =
      (fun p : S × Matrix (Fin (r + 1)) (Fin (s + 1)) ℝ =>
        (p.1, (p.2 *ᵥ w p.1, p.2ᵀ *ᵥ u p.1))) := by
    funext p
    exact congrArg (fun reply => (p.1, reply))
      (exposedTwoSidedReply_eq_oracle b c (u p.1) (w p.1)
        (hunitU p.1) (hunitW p.1) p.2)
  rw [heq] at hind
  simpa only [Function.comp_def, id_eq] using hind

end Queries

end
end Matvec
