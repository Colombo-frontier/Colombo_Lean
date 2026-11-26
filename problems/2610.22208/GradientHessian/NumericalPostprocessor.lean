import GradientHessian.NumericalPreprocessor

noncomputable section
namespace GradientHessian.NumericalPostprocessor
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

abbrev RuntimeState := NumericalPreprocessor.RuntimeState (d := d) (n := n) (r := r) (J := J)
  (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t × EuclideanSpace ℝ (Fin r) × Bool

def cache (j : Fin (4096*J^2+1))
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t) : Cache d J :=
  (Function.update (NumericalPreprocessor.forcing B j s.1.1.1) j
    (InverseGate.H₀ • LowRank.matrixEuclideanMap B s.2.1),s.1.2.1.2)

def halt (j : Fin (4096*J^2+1))
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t) : Bool :=
  NumericalDriverInstructions.finished s.1.2.2 || taskDisclosed leaf j (ControllerDriverMonotonicity.stateOf s.1.2.2)

def normalInstruction : Config (t+1) (4096*J^2+1) ell S
    (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) (Action t (4096*J^2)) → Bool
  | .pending _ _ _ (.normal p _) => decide (p.kind=.ordinary)
  | _ => false

def mode (j : Fin (4096*J^2+1))
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t) : Fin 4 :=
  if halt t leaf j s then 0 else
  if normalInstruction t s.1.2.2 && !s.2.2 then 3 else
  if NumericalDriverInstructions.product leaf (taskDisclosed leaf j) s.1.2.2 then 2 else 1

def stepReply (K : ℝ) (j : Fin (4096*J^2+1))
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t)
    (Ay : Fin d → ℝ) : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t :=
  ((s.1.1,s.1.2.1,NumericalRuntime.advance P B fallback t leaf policy K (taskDisclosed leaf j)
    s.1.1.2.1 (cache B t j s) ((NumericalOrdinaryProcedure.coordinates d).symm Ay) s.1.2.2),s.2.1,false)

def query (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t) : Fin d → ℝ :=
  NumericalPreprocessor.query t s.1

def test (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t) : EuclideanSpace ℝ (Fin d) :=
  BoundedNumericalTest.test (CensoredOracle.numericalMap t (NumericalDriverInstructions.point s.1.2.2))

def selected (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t) :
    RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t :=
  (s.1,s.2.1,true)

def initial (s : NumericalPreprocessor.RuntimeState (d := d) (n := n) (r := r) (J := J)
    (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t)
    (w : EuclideanSpace ℝ (Fin r)) :
    RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t :=
  (s,w,false)

def enabled (j : Fin (4096*J^2+1))
    (s : NumericalPreprocessor.RuntimeState (d := d) (n := n) (r := r) (J := J)
      (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t) : Bool :=
  decide (NumericalDriverInstructions.finished s.2.2=false ∧
    TaskState.current (ControllerDriverMonotonicity.stateOf s.2.2)=some leaf ∧
    ((ControllerDriverMonotonicity.stateOf s.2.2).completed leaf).val=j.val)

theorem test_norm (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
    (E := E) (H := H) (Seed := Seed) (S := S) t) : ‖test t s‖ ≤ 1 :=
  BoundedNumericalTest.test_norm _

theorem selection_preserves_configuration
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
      (E := E) (H := H) (Seed := Seed) (S := S) t) :
    (selected t s).1.2.2=s.1.2.2 := rfl

end GradientHessian.NumericalPostprocessor