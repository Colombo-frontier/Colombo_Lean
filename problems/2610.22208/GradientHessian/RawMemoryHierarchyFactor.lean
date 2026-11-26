import GradientHessian.RawMemoryFactor
import GradientHessian.RawSubtreeFactor

/-! Old and inner memory directions at arbitrary coefficient addresses are
independent sphere factors of the complete raw hierarchy. -/

noncomputable section
namespace GradientHessian.RawMemoryHierarchyFactor
open MeasureTheory Matrix RawHierarchy ProductCoordinateFactor

abbrev OldRest (d n r J : ℕ) (E : Type) (H : ℕ → Type) (depth : ℕ) :=
  RawMemoryFactor.OldRest d n r J E × RawSubtreeFactor.Rest d n r J E H 0 depth
abbrev InnerRest (d n r J : ℕ) (E : Type) (H : ℕ → Type) (depth : ℕ) :=
  RawMemoryFactor.InnerRest d n r J E × RawSubtreeFactor.Rest d n r J E H 0 depth

variable {d n r J : ℕ} {E : Type} {H : ℕ → Type}
variable [MeasurableSpace E] [∀ t, MeasurableSpace (H t)]

def oldFactor (depth : ℕ) (w : RawSubtreeFactor.Word depth) (i : Fin 8)
    (j : Fin (FirstHeight.depth (4096*J^2+1)+2)) :
    Raw d n r J E H (0+depth) ≃ᵐ E × OldRest d n r J E H depth :=
  (RawSubtreeFactor.factor 0 depth w).trans (leftFactor (RawMemoryFactor.oldFactor i j))

def innerFactor (depth : ℕ) (w : RawSubtreeFactor.Word depth) (i : Fin 8)
    (j : Fin (4096*J^2+1)) (k : Fin (Inner.absoluteDepth+2)) :
    Raw d n r J E H (0+depth) ≃ᵐ E × InnerRest d n r J E H depth :=
  (RawSubtreeFactor.factor 0 depth w).trans (leftFactor (RawMemoryFactor.innerFactor i j k))

theorem oldFactor_direction (depth : ℕ) (w : RawSubtreeFactor.Word depth) (i : Fin 8)
    (j : Fin (FirstHeight.depth (4096*J^2+1)+2)) (x : Raw d n r J E H (0+depth)) :
    (oldFactor depth w i j x).1=(RawSubtreeFactor.selectedRaw 0 depth w x).2.2.2 i j := by
  change (RawSubtreeFactor.factor 0 depth w x).1.2.2.2 i j=_
  rw [RawSubtreeFactor.factor_target]

theorem innerFactor_direction (depth : ℕ) (w : RawSubtreeFactor.Word depth) (i : Fin 8)
    (j : Fin (4096*J^2+1)) (k : Fin (Inner.absoluteDepth+2)) (x : Raw d n r J E H (0+depth)) :
    (innerFactor depth w i j k x).1=(RawSubtreeFactor.selectedRaw 0 depth w x).2.2.1 i j k := by
  change (RawSubtreeFactor.factor 0 depth w x).1.2.2.1 i j k=_
  rw [RawSubtreeFactor.factor_target]

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [BorelSpace E] [FiniteDimensional ℝ E]
  [∀ t, NormedAddCommGroup (H t)] [∀ t, InnerProductSpace ℝ (H t)]
  [∀ t, BorelSpace (H t)] [∀ t, FiniteDimensional ℝ (H t)]

def oldRestLaw (P : Matrix (Fin d) (Fin d) ℝ) (depth : ℕ) : Measure (OldRest d n r J E H depth) :=
  (RawMemoryFactor.oldRestLaw P J r).prod (RawSubtreeFactor.restLaw 0 P depth)

def innerRestLaw (P : Matrix (Fin d) (Fin d) ℝ) (depth : ℕ) : Measure (InnerRest d n r J E H depth) :=
  (RawMemoryFactor.innerRestLaw P J r).prod (RawSubtreeFactor.restLaw 0 P depth)

theorem oldRestLaw_probability (P : Matrix (Fin d) (Fin d) ℝ)
    [IsProbabilityMeasure (ConditionedSource.sourceLaw (n := n) P J)] (depth : ℕ) :
    IsProbabilityMeasure (oldRestLaw (n := n) (r := r) (J := J) (E := E) (H := H) P depth) := by
  letI := RawMemoryFactor.oldRestLaw_probability (n := n) (r := r) (J := J) (E := E) P
  letI := RawSubtreeFactor.restLaw_probability (n := n) (r := r) (J := J) (E := E) (H := H) 0 P depth
  unfold oldRestLaw
  infer_instance

theorem innerRestLaw_probability (P : Matrix (Fin d) (Fin d) ℝ)
    [IsProbabilityMeasure (ConditionedSource.sourceLaw (n := n) P J)] (depth : ℕ) :
    IsProbabilityMeasure (innerRestLaw (n := n) (r := r) (J := J) (E := E) (H := H) P depth) := by
  letI := RawMemoryFactor.innerRestLaw_probability (n := n) (r := r) (J := J) (E := E) P
  letI := RawSubtreeFactor.restLaw_probability (n := n) (r := r) (J := J) (E := E) (H := H) 0 P depth
  unfold innerRestLaw
  infer_instance

theorem oldFactor_preserving (P : Matrix (Fin d) (Fin d) ℝ)
    [IsProbabilityMeasure (ConditionedSource.sourceLaw (n := n) P J)]
    (depth : ℕ) (w : RawSubtreeFactor.Word depth) (i : Fin 8)
    (j : Fin (FirstHeight.depth (4096*J^2+1)+2)) :
    MeasurePreserving (oldFactor (d := d) (n := n) (r := r) (J := J) (E := E) (H := H) depth w i j)
      (RawHierarchy.law P (0+depth)) ((SphereGaussian.sphereLaw E).prod (oldRestLaw P depth)) := by
  letI := RawFirstHeight.law_probability (n := n) (r := r) (J := J) (E := E) P
  letI := RawMemoryFactor.oldRestLaw_probability (n := n) (r := r) (J := J) (E := E) P
  letI := RawSubtreeFactor.restLaw_probability (n := n) (r := r) (J := J) (E := E) (H := H) 0 P depth
  exact (leftFactor_preserving (RawMemoryFactor.oldFactor i j) (RawFirstHeight.law P J r)
    _ (RawMemoryFactor.oldRestLaw P J r) (RawSubtreeFactor.restLaw 0 P depth)
    (RawMemoryFactor.oldFactor_preserving P i j)).comp (RawSubtreeFactor.factor_preserving 0 P depth w)

theorem innerFactor_preserving (P : Matrix (Fin d) (Fin d) ℝ)
    [IsProbabilityMeasure (ConditionedSource.sourceLaw (n := n) P J)]
    (depth : ℕ) (w : RawSubtreeFactor.Word depth) (i : Fin 8)
    (j : Fin (4096*J^2+1)) (k : Fin (Inner.absoluteDepth+2)) :
    MeasurePreserving (innerFactor (d := d) (n := n) (r := r) (J := J) (E := E) (H := H) depth w i j k)
      (RawHierarchy.law P (0+depth)) ((SphereGaussian.sphereLaw E).prod (innerRestLaw P depth)) := by
  letI := RawFirstHeight.law_probability (n := n) (r := r) (J := J) (E := E) P
  letI := RawMemoryFactor.innerRestLaw_probability (n := n) (r := r) (J := J) (E := E) P
  letI := RawSubtreeFactor.restLaw_probability (n := n) (r := r) (J := J) (E := E) (H := H) 0 P depth
  exact (leftFactor_preserving (RawMemoryFactor.innerFactor i j k) (RawFirstHeight.law P J r)
    _ (RawMemoryFactor.innerRestLaw P J r) (RawSubtreeFactor.restLaw 0 P depth)
    (RawMemoryFactor.innerFactor_preserving P i j k)).comp (RawSubtreeFactor.factor_preserving 0 P depth w)

end GradientHessian.RawMemoryHierarchyFactor
