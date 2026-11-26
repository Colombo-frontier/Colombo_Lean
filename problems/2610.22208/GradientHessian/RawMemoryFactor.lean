import GradientHessian.RawFirstFactor
import GradientHessian.ProductCoordinateFactor

/-! Actual independent factors for old and inner memory directions at a
height-one node. All matrices and marks remain in the external-data factor. -/

noncomputable section
namespace GradientHessian.RawMemoryFactor
open MeasureTheory Matrix RawFirstFactor ProductRearrangement ProductCoordinateFactor

abbrev Header (d n r J : ℕ) :=
  (Fin 8 → Matrix (Fin d) (Fin n) ℝ) × (Fin 8 → Marks r J)
abbrev OldVectorRest (J : ℕ) (E : Type) :=
  (Fin (FirstHeight.depth (4096*J^2+1)+1) → E) ×
    (Fin 7 → Fin (FirstHeight.depth (4096*J^2+1)+2) → E)
abbrev InnerVectorRest (J : ℕ) (E : Type) :=
  ((Fin (Inner.absoluteDepth+1) → E) × (Fin (4096*J^2) → Fin (Inner.absoluteDepth+2) → E)) ×
    (Fin 7 → Fin (4096*J^2+1) → Fin (Inner.absoluteDepth+2) → E)
abbrev OldRest (d n r J : ℕ) (E : Type) := (Header d n r J × InnerDirections J E) × OldVectorRest J E
abbrev InnerRest (d n r J : ℕ) (E : Type) := Header d n r J × InnerVectorRest J E × OuterDirections J E

variable {d n r J : ℕ} {E : Type} [MeasurableSpace E]

def oldVectorFactor (i : Fin 8) (j : Fin (FirstHeight.depth (4096*J^2+1)+2)) :
    OuterDirections J E ≃ᵐ E × OldVectorRest J E := liftArray (split j) i

def innerVectorFactor (i : Fin 8) (j : Fin (4096*J^2+1)) (k : Fin (Inner.absoluteDepth+2)) :
    InnerDirections J E ≃ᵐ E × InnerVectorRest J E := liftArray (liftArray (split k) j) i

def regroup : RawFirstHeight.Raw d n r J E ≃ᵐ Header d n r J × InnerDirections J E × OuterDirections J E :=
  MeasurableEquiv.prodAssoc.symm

def oldFactor (i : Fin 8) (j : Fin (FirstHeight.depth (4096*J^2+1)+2)) :
    RawFirstHeight.Raw d n r J E ≃ᵐ E × OldRest d n r J E :=
  regroup.trans (MeasurableEquiv.prodAssoc.symm.trans (rightFactor (oldVectorFactor i j)))

def innerFactor (i : Fin 8) (j : Fin (4096*J^2+1)) (k : Fin (Inner.absoluteDepth+2)) :
    RawFirstHeight.Raw d n r J E ≃ᵐ E × InnerRest d n r J E :=
  regroup.trans (rightFactor (leftFactor (innerVectorFactor i j k)))

theorem oldFactor_direction (i : Fin 8) (j : Fin (FirstHeight.depth (4096*J^2+1)+2))
    (x : RawFirstHeight.Raw d n r J E) : (oldFactor i j x).1=x.2.2.2 i j := rfl

theorem innerFactor_direction (i : Fin 8) (j : Fin (4096*J^2+1)) (k : Fin (Inner.absoluteDepth+2))
    (x : RawFirstHeight.Raw d n r J E) : (innerFactor i j k x).1=x.2.2.1 i j k := rfl

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [BorelSpace E] [FiniteDimensional ℝ E]

def headerLaw (P : Matrix (Fin d) (Fin d) ℝ) (J r : ℕ) : Measure (Header d n r J) :=
  (Measure.pi (fun _ : Fin 8 => ConditionedSource.sourceLaw (n := n) P J)).prod
    (Measure.pi (fun _ : Fin 8 => marksLaw r J))

def oldVectorRestLaw (J : ℕ) (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] : Measure (OldVectorRest J E) :=
  (Measure.pi (fun _ => SphereGaussian.sphereLaw E)).prod
    (Measure.pi (fun _ => Measure.pi (fun _ => SphereGaussian.sphereLaw E)))

def innerVectorRestLaw (J : ℕ) (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] : Measure (InnerVectorRest J E) :=
  ((Measure.pi (fun _ => SphereGaussian.sphereLaw E)).prod
    (Measure.pi (fun _ => Measure.pi (fun _ => SphereGaussian.sphereLaw E)))).prod
      (Measure.pi (fun _ => Measure.pi (fun _ => Measure.pi (fun _ => SphereGaussian.sphereLaw E))))

def oldRestLaw (P : Matrix (Fin d) (Fin d) ℝ) (J r : ℕ) : Measure (OldRest d n r J E) :=
  ((headerLaw P J r).prod (innerLaw J E)).prod (oldVectorRestLaw J E)

def innerRestLaw (P : Matrix (Fin d) (Fin d) ℝ) (J r : ℕ) : Measure (InnerRest d n r J E) :=
  (headerLaw P J r).prod ((innerVectorRestLaw J E).prod (outerLaw J E))

set_option synthInstance.maxSize 512 in
theorem headerLaw_probability (P : Matrix (Fin d) (Fin d) ℝ)
    [IsProbabilityMeasure (ConditionedSource.sourceLaw (n := n) P J)] :
    IsProbabilityMeasure (headerLaw (n := n) P J r) := by unfold headerLaw; infer_instance

set_option synthInstance.maxSize 512 in
instance oldVectorRestLaw_probability : IsProbabilityMeasure (oldVectorRestLaw J E) := by
  unfold oldVectorRestLaw
  infer_instance

set_option synthInstance.maxSize 512 in
instance innerVectorRestLaw_probability : IsProbabilityMeasure (innerVectorRestLaw J E) := by
  unfold innerVectorRestLaw
  infer_instance

theorem oldRestLaw_probability (P : Matrix (Fin d) (Fin d) ℝ)
    [IsProbabilityMeasure (ConditionedSource.sourceLaw (n := n) P J)] :
    IsProbabilityMeasure (oldRestLaw (E := E) (n := n) P J r) := by
  letI := headerLaw_probability (n := n) (r := r) (J := J) P
  unfold oldRestLaw
  infer_instance

theorem innerRestLaw_probability (P : Matrix (Fin d) (Fin d) ℝ)
    [IsProbabilityMeasure (ConditionedSource.sourceLaw (n := n) P J)] :
    IsProbabilityMeasure (innerRestLaw (E := E) (n := n) P J r) := by
  letI := headerLaw_probability (n := n) (r := r) (J := J) P
  unfold innerRestLaw
  infer_instance

theorem oldVectorFactor_preserving (i : Fin 8) (j : Fin (FirstHeight.depth (4096*J^2+1)+2)) :
    MeasurePreserving (oldVectorFactor (E := E) i j) (outerLaw J E)
      ((SphereGaussian.sphereLaw E).prod (oldVectorRestLaw J E)) :=
  liftArray_preserving (split j) i _ _ _ (split_preserving j (SphereGaussian.sphereLaw E))

set_option synthInstance.maxSize 512 in
theorem innerVectorFactor_preserving (i : Fin 8) (j : Fin (4096*J^2+1)) (k : Fin (Inner.absoluteDepth+2)) :
    MeasurePreserving (innerVectorFactor (E := E) i j k) (innerLaw J E)
      ((SphereGaussian.sphereLaw E).prod (innerVectorRestLaw J E)) :=
  liftArray_preserving (liftArray (split k) j) i _ _ _
    (liftArray_preserving (split k) j _ _ _ (split_preserving k (SphereGaussian.sphereLaw E)))

theorem regroup_preserving (P : Matrix (Fin d) (Fin d) ℝ)
    [IsProbabilityMeasure (ConditionedSource.sourceLaw (n := n) P J)] :
    MeasurePreserving (regroup (d := d) (n := n) (r := r) (J := J) (E := E)) (RawFirstHeight.law P J r)
      ((headerLaw P J r).prod ((innerLaw J E).prod (outerLaw J E))) :=
  (measurePreserving_prodAssoc (Measure.pi (fun _ : Fin 8 => ConditionedSource.sourceLaw (n := n) P J))
    (Measure.pi (fun _ : Fin 8 => marksLaw r J)) ((innerLaw J E).prod (outerLaw J E))).symm
      MeasurableEquiv.prodAssoc

theorem oldFactor_preserving (P : Matrix (Fin d) (Fin d) ℝ)
    [IsProbabilityMeasure (ConditionedSource.sourceLaw (n := n) P J)]
    (i : Fin 8) (j : Fin (FirstHeight.depth (4096*J^2+1)+2)) :
    MeasurePreserving (oldFactor (d := d) (n := n) (r := r) (J := J) (E := E) i j)
      (RawFirstHeight.law P J r) ((SphereGaussian.sphereLaw E).prod (oldRestLaw P J r)) := by
  letI := headerLaw_probability (n := n) (r := r) (J := J) P
  exact (rightFactor_preserving (oldVectorFactor i j) (outerLaw J E) _ (oldVectorRestLaw J E)
    ((headerLaw P J r).prod (innerLaw J E)) (oldVectorFactor_preserving i j)).comp
      (((measurePreserving_prodAssoc (headerLaw P J r) (innerLaw J E) (outerLaw J E)).symm
        MeasurableEquiv.prodAssoc).comp (regroup_preserving P))

theorem innerFactor_preserving (P : Matrix (Fin d) (Fin d) ℝ)
    [IsProbabilityMeasure (ConditionedSource.sourceLaw (n := n) P J)]
    (i : Fin 8) (j : Fin (4096*J^2+1)) (k : Fin (Inner.absoluteDepth+2)) :
    MeasurePreserving (innerFactor (d := d) (n := n) (r := r) (J := J) (E := E) i j k)
      (RawFirstHeight.law P J r) ((SphereGaussian.sphereLaw E).prod (innerRestLaw P J r)) := by
  letI := headerLaw_probability (n := n) (r := r) (J := J) P
  exact (rightFactor_preserving (leftFactor (innerVectorFactor i j k))
    ((innerLaw J E).prod (outerLaw J E)) _ ((innerVectorRestLaw J E).prod (outerLaw J E))
    (headerLaw P J r)
    (leftFactor_preserving (innerVectorFactor i j k) (innerLaw J E) _ (innerVectorRestLaw J E)
      (outerLaw J E) (innerVectorFactor_preserving i j k))).comp (regroup_preserving P)

end GradientHessian.RawMemoryFactor
