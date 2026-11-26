import GradientHessian.RawFirstHeight
import GradientHessian.ProductRearrangement

/-! Factor the actual height-one product around one leaf's matrix and entire
mark sequence. All remaining variables form the independent second factor. -/

noncomputable section
namespace GradientHessian.RawFirstFactor
open MeasureTheory Matrix ProductRearrangement

abbrev Marks (r J : ℕ) := Fin (4096*J^2+1) → EuclideanSpace ℝ (Fin r)
abbrev InnerDirections (J : ℕ) (E : Type) :=
  Fin 8 → Fin (4096*J^2+1) → Fin (Inner.absoluteDepth+2) → E
abbrev OuterDirections (J : ℕ) (E : Type) := Fin 8 → Fin (FirstHeight.depth (4096*J^2+1)+2) → E
abbrev Target (d n r J : ℕ) := Matrix (Fin d) (Fin n) ℝ × Marks r J
abbrev Rest (d n r J : ℕ) (E : Type) :=
  (Fin 7 → Matrix (Fin d) (Fin n) ℝ) × (Fin 7 → Marks r J) ×
    InnerDirections J E × OuterDirections J E

variable {d n r J : ℕ} {E : Type} [MeasurableSpace E]

def factor (i : Fin 8) : RawFirstHeight.Raw d n r J E ≃ᵐ Target d n r J × Rest d n r J E :=
  ((split i).prodCongr ((split i).prodCongr
    (MeasurableEquiv.refl (InnerDirections J E × OuterDirections J E)))).trans pairHeads

theorem factor_target (i : Fin 8) (x : RawFirstHeight.Raw d n r J E) :
    (factor i x).1 = (x.1 i,x.2.1 i) := rfl

theorem factor_rest_matrices (i : Fin 8) (x : RawFirstHeight.Raw d n r J E) (j : Fin 7) :
    (factor i x).2.1 j = x.1 (i.succAbove j) := rfl

theorem factor_rest_marks (i : Fin 8) (x : RawFirstHeight.Raw d n r J E) (j : Fin 7) :
    (factor i x).2.2.1 j = x.2.1 (i.succAbove j) := rfl

def marksLaw (r J : ℕ) : Measure (Marks r J) :=
  Measure.pi (fun _ => SphereGaussian.sphereLaw (EuclideanSpace ℝ (Fin r)))

instance marksLaw_probability : IsProbabilityMeasure (marksLaw r J) := by unfold marksLaw; infer_instance

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [BorelSpace E] [FiniteDimensional ℝ E]

def innerLaw (J : ℕ) (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] : Measure (InnerDirections J E) :=
  Measure.pi (fun _ => Measure.pi (fun _ => Measure.pi (fun _ => SphereGaussian.sphereLaw E)))

def outerLaw (J : ℕ) (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] : Measure (OuterDirections J E) :=
  Measure.pi (fun _ => Measure.pi (fun _ => SphereGaussian.sphereLaw E))

set_option synthInstance.maxSize 512 in
instance innerLaw_probability : IsProbabilityMeasure (innerLaw J E) := by unfold innerLaw; infer_instance
instance outerLaw_probability : IsProbabilityMeasure (outerLaw J E) := by unfold outerLaw; infer_instance

def targetLaw (P : Matrix (Fin d) (Fin d) ℝ) (J r : ℕ) : Measure (Target d n r J) :=
  (ConditionedSource.sourceLaw P J).prod (marksLaw r J)

def restLaw (P : Matrix (Fin d) (Fin d) ℝ) (J r : ℕ) : Measure (Rest d n r J E) :=
  (Measure.pi (fun _ : Fin 7 => ConditionedSource.sourceLaw (n := n) P J)).prod
    ((Measure.pi (fun _ : Fin 7 => marksLaw r J)).prod ((innerLaw J E).prod (outerLaw J E)))

theorem targetLaw_probability (P : Matrix (Fin d) (Fin d) ℝ)
    [IsProbabilityMeasure (ConditionedSource.sourceLaw (n := n) P J)] :
    IsProbabilityMeasure (targetLaw (n := n) P J r) := by unfold targetLaw; infer_instance

set_option synthInstance.maxSize 512 in
theorem restLaw_probability (P : Matrix (Fin d) (Fin d) ℝ)
    [IsProbabilityMeasure (ConditionedSource.sourceLaw (n := n) P J)] :
    IsProbabilityMeasure (restLaw (E := E) (n := n) P J r) := by unfold restLaw; infer_instance

set_option synthInstance.maxSize 512 in
theorem factor_preserving (P : Matrix (Fin d) (Fin d) ℝ)
    [IsProbabilityMeasure (ConditionedSource.sourceLaw (n := n) P J)] (i : Fin 8) :
    MeasurePreserving (factor (d := d) (n := n) (r := r) (J := J) (E := E) i)
      (RawFirstHeight.law P J r)
      ((targetLaw (n := n) P J r).prod (restLaw (E := E) (n := n) P J r)) := by
  exact (pairHeads_preserving (ConditionedSource.sourceLaw (n := n) P J)
    (Measure.pi (fun _ : Fin 7 => ConditionedSource.sourceLaw (n := n) P J))
    (marksLaw r J) (Measure.pi (fun _ : Fin 7 => marksLaw r J))
    ((innerLaw J E).prod (outerLaw J E))).comp
      ((split_preserving i (ConditionedSource.sourceLaw (n := n) P J)).prod
        ((split_preserving i (marksLaw r J)).prod
          (MeasurePreserving.id ((innerLaw J E).prod (outerLaw J E)))))

end GradientHessian.RawFirstFactor
