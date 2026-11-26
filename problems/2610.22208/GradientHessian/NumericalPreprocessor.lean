import GradientHessian.NumericalRuntime
import GradientHessian.RawNumericalExperiment
import GradientHessian.DisclosureCappedProgram

/-! Literal charged preprocessing state: independent auxiliary data, a finite
readout cache, and the preserved chronological policy/controller configuration. -/

noncomputable section
namespace GradientHessian.NumericalPreprocessor
open Classical HigherHierarchy HierarchyAddresses CensoredHierarchy FrontierState TaskState
  ComparisonController ComparisonControllerReplay ControllerMeasurable ControllerPolicyDriver
  GeometricRepair NumericalCachedOracle

variable {d n r J ell : ℕ} {E : Type} {H : ℕ → Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [∀ h,MeasurableSpace (H h)] [∀ h,BorelSpace (H h)] [∀ h,FiniteDimensional ℝ (H h)]
variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ)
  (t : ℕ) (leaf : Leaf (t+1))
variable [MeasurableSpace (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)]
  [BorelSpace (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)]
  [MeasurableSpace (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))]
  [BorelSpace (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))]
  [MeasurableSpace (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ) ×
    (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ]
      Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))]
  [BorelSpace (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ) ×
    (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ]
      Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))]
variable {Seed S : Type*} [MeasurableSpace Seed] [MeasurableSpace S]
variable (policy : Machine.Policy Seed S (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)
  (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))
  (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ) ×
    (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ]
      Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ)))

abbrev Store (d J : ℕ) := (Fin (4096*J^2+1) → Bool) × (Fin (4096*J^2+1) → EuclideanSpace ℝ (Fin d))

abbrev RuntimeState := RawNumericalExperiment.Auxiliary d n r J E H t Seed × Store d J ×
  Config (t+1) (4096*J^2+1) ell S (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) (Action t (4096*J^2))

def marks (j : Fin (4096*J^2+1)) (w : Fin (4096*J^2) → EuclideanSpace ℝ (Fin r)) :=
  (ProductRearrangement.split j).symm (0,w)

def forcing (j : Fin (4096*J^2+1)) (w : Fin (4096*J^2) → EuclideanSpace ℝ (Fin r)) :
    Fin (4096*J^2+1) → EuclideanSpace ℝ (Fin d) :=
  fun k => InverseGate.H₀ • LowRank.matrixEuclideanMap B (marks j w k)

def cache (j : Fin (4096*J^2+1)) (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t) : Cache d J :=
  (forcing B j s.1.1,s.2.1.2)

def index (j : Fin (4096*J^2+1)) (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t) :=
  NumericalDriverInstructions.readoutIndex leaf j s.2.1.1 (ControllerDriverMonotonicity.stateOf s.2.2)

def halt (j : Fin (4096*J^2+1)) (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t) : Bool :=
  NumericalDriverInstructions.finished s.2.2 || markSupplied leaf j (ControllerDriverMonotonicity.stateOf s.2.2)

def mode (j : Fin (4096*J^2+1)) (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t) : Fin 4 :=
  if halt t leaf j s then 0 else if (index t leaf j s).isSome then 3
  else if NumericalDriverInstructions.product leaf (markSupplied leaf j) s.2.2 then 2 else 1

def stepReply (K : ℝ) (j : Fin (4096*J^2+1))
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t) (Ay : Fin d → ℝ) :
    RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t :=
  (s.1,s.2.1,NumericalRuntime.advance P B fallback t leaf policy K (markSupplied leaf j)
    s.1.2.1 (cache B t j s) ((NumericalOrdinaryProcedure.coordinates d).symm Ay) s.2.2)

def query (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t) : Fin d → ℝ :=
  NumericalOrdinaryProcedure.coordinates d (CensoredOracle.numericalMap t (NumericalDriverInstructions.point s.2.2))

def requestedMark (j : Fin (4096*J^2+1))
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t) : Fin d → ℝ :=
  match index t leaf j s with
  | none => 0
  | some k => NumericalOrdinaryProcedure.coordinates d (LowRank.matrixEuclideanMap B (marks j s.1.1 k))

def accept (j : Fin (4096*J^2+1))
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t)
    (a : Fin d → ℝ) : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t :=
  match index t leaf j s with
  | none => s
  | some k => (s.1,(Function.update s.2.1.1 k true,
      Function.update s.2.1.2 k ((NumericalOrdinaryProcedure.coordinates d).symm a)),s.2.2)

def initial (N : ℕ) (w : RawNumericalExperiment.Auxiliary d n r J E H t Seed) :
    RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t :=
  (w,(fun _ => false,fun _ => 0),ControllerPolicyDriver.initial policy N w.2.2 TaskState.initial)

theorem accept_configuration (j : Fin (4096*J^2+1))
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t) (a : Fin d → ℝ) :
    (accept t leaf j s a).2.2=s.2.2 := by cases h : index t leaf j s <;> simp [accept,h]

theorem accept_external (j : Fin (4096*J^2+1))
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t) (a : Fin d → ℝ) :
    (accept t leaf j s a).1=s.1 := by cases h : index t leaf j s <;> simp [accept,h]

theorem accept_loaded (j k : Fin (4096*J^2+1))
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t) (a : Fin d → ℝ)
    (hk : index t leaf j s=some k) :
    (accept t leaf j s a).2.1.1 k=true ∧
      (accept t leaf j s a).2.1.2 k=(NumericalOrdinaryProcedure.coordinates d).symm a := by
  simp only [accept,hk,Function.update_self,and_self]

end GradientHessian.NumericalPreprocessor