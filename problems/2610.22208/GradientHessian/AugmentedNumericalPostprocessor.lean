import GradientHessian.AugmentedNumericalPreprocessor
import GradientHessian.SelectionCappedProgram

/-! Augmented postprocessing after the target forcing direction is supplied.
Initialization is still suspended when the target was initially active. Each
normal ordinary point is selected before feedback, with separately capped
matrix products and selected tests. -/

noncomputable section
namespace GradientHessian.AugmentedNumericalPostprocessor
open Classical HigherHierarchy HierarchyAddresses FrontierState TaskState
  NumericalCachedOracle AugmentedNumericalDriver

variable {d n r J ell : ℕ} {E : Type} {H : ℕ → Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [∀ h,MeasurableSpace (H h)] [∀ h,BorelSpace (H h)] [∀ h,FiniteDimensional ℝ (H h)]
variable {Seed S : Type*} [MeasurableSpace Seed] [MeasurableSpace S]
variable (t : ℕ)
variable [MeasurableSpace (DirectionPolicyReplay.Point d J E H t)]
  [BorelSpace (DirectionPolicyReplay.Point d J E H t)]
  [MeasurableSpace (DirectionPolicyReplay.Ordinary d J E H t)]
  [BorelSpace (DirectionPolicyReplay.Ordinary d J E H t)]
  [MeasurableSpace (DirectionPolicyReplay.Rich d J E H t)]
  [BorelSpace (DirectionPolicyReplay.Rich d J E H t)]

abbrev RuntimeState := AugmentedNumericalPreprocessor.RuntimeState
  (d := d) (n := n) (r := r) (J := J) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t ×
    EuclideanSpace ℝ (Fin r) × Bool

local notation "Pre" => AugmentedNumericalPreprocessor.RuntimeState (d := d) (n := n) (r := r)
  (J := J) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t
local notation "Run" => RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
  (E := E) (H := H) (Seed := Seed) (S := S) t

variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ)
  (leaf : Leaf (t+1))
  (policy : Machine.Policy (Seed × AugmentedPolicy.Packet d J E H t ell) S
    (DirectionPolicyReplay.Point d J E H t)
    (AugmentedPolicy.Ordinary d J E H t ell) (AugmentedPolicy.Rich d J E H t ell))

def cache (j : Fin (4096*J^2+1)) (s : Run) : Cache d J :=
  (Function.update (NumericalPreprocessor.forcing B j s.1.1.1) j
    (InverseGate.H₀ • LowRank.matrixEuclideanMap B s.2.1),s.1.2.1.2)

def halt (j : Fin (4096*J^2+1)) (s : Run) : Bool :=
  AugmentedNumericalDriver.finished t s.1.2.2 ||
    ComparisonControllerReplay.taskDisclosed leaf j (AugmentedNumericalDriver.state t s.1.2.2)

def mode (j : Fin (4096*J^2+1)) (s : Run) : Fin 4 :=
  if halt t leaf j s then 0 else
    if AugmentedNumericalDriver.normalInstruction t s.1.2.2 && !s.2.2 then 3 else
    if AugmentedNumericalDriver.product t leaf (ComparisonControllerReplay.taskDisclosed leaf j) s.1.2.2 then 2 else 1

def stepReply (K : ℝ) (N : ℕ) (j : Fin (4096*J^2+1)) (s : Run) (Ay : Fin d → ℝ) : Run :=
  ((s.1.1,s.1.2.1,AugmentedNumericalDriver.advance t P B fallback leaf policy K N
    (ComparisonControllerReplay.taskDisclosed leaf j) s.1.1.2.2 s.1.1.2.1 (cache t B j s)
      ((NumericalOrdinaryProcedure.coordinates d).symm Ay) s.1.2.2),s.2.1,false)

def query (s : Run) : Fin d → ℝ := AugmentedNumericalPreprocessor.query t s.1

def test (s : Run) : EuclideanSpace ℝ (Fin d) :=
  BoundedNumericalTest.test (CensoredOracle.numericalMap t (AugmentedNumericalDriver.point t s.1.2.2))

def selected (s : Run) : Run := (s.1,s.2.1,true)

def initial (s : Pre) (w : EuclideanSpace ℝ (Fin r)) : Run := (s,w,false)

def enabled (j : Fin (4096*J^2+1)) (s : Pre) : Bool :=
  decide (AugmentedNumericalDriver.finished t s.2.2=false ∧
    TaskState.current (AugmentedNumericalDriver.state t s.2.2)=some leaf ∧
    ((AugmentedNumericalDriver.state t s.2.2).completed leaf).val=j.val)

theorem cache_measurable (j : Fin (4096*J^2+1)) : Measurable (cache t B j : Run → Cache d J) := by
  apply Measurable.prodMk
  · exact (measurable_update' (a := j)).comp
      (((NumericalPreprocessor.forcing_measurable B j).comp
        (measurable_fst.comp (measurable_fst.comp measurable_fst))).prodMk
        (measurable_const.smul ((LowRank.matrixEuclideanMap B).continuous.measurable.comp
          (measurable_fst.comp measurable_snd))))
  · fun_prop

theorem halt_measurable (j : Fin (4096*J^2+1)) : Measurable (halt t leaf j : Run → Bool) :=
  (measurable_of_countable (fun q : Bool × Bool => q.1 || q.2)).comp
    (((AugmentedNumericalDriver.finished_measurable t).comp
      (measurable_snd.comp (measurable_snd.comp measurable_fst))).prodMk
      ((measurable_of_countable (ComparisonControllerReplay.taskDisclosed leaf j)).comp
        ((AugmentedNumericalDriver.state_measurable t).comp
          (measurable_snd.comp (measurable_snd.comp measurable_fst)))))

theorem mode_measurable (j : Fin (4096*J^2+1)) : Measurable (mode t leaf j : Run → Fin 4) := by
  have hm : Measurable (fun s : Run =>
      (halt t leaf j s,AugmentedNumericalDriver.normalInstruction t s.1.2.2,s.2.2,
        AugmentedNumericalDriver.product t leaf (ComparisonControllerReplay.taskDisclosed leaf j) s.1.2.2)) :=
    (halt_measurable t leaf j).prodMk
      (((AugmentedNumericalDriver.normalInstruction_measurable t).comp
        (measurable_snd.comp (measurable_snd.comp measurable_fst))).prodMk
        ((measurable_snd.comp measurable_snd).prodMk
          ((AugmentedNumericalDriver.product_measurable t leaf (ComparisonControllerReplay.taskDisclosed leaf j)).comp
            (measurable_snd.comp (measurable_snd.comp measurable_fst)))))
  exact (measurable_of_countable (fun z : Bool × Bool × Bool × Bool =>
    if z.1 then (0 : Fin 4) else if z.2.1 && !z.2.2.1 then 3 else if z.2.2.2 then 2 else 1)).comp hm

theorem stepReply_measurable {K : ℝ} (hK : 0<K) (N : ℕ) (j : Fin (4096*J^2+1)) :
    Measurable (fun q : Run × (Fin d → ℝ) => stepReply t P B fallback leaf policy K N j q.1 q.2) := by
  have hm : Measurable (fun q : Run × (Fin d → ℝ) =>
      ((((q.1.1.1.2.1,cache t B j q.1),q.1.1.1.2.2),(NumericalOrdinaryProcedure.coordinates d).symm q.2),q.1.1.2.2)) := by
    apply Measurable.prodMk
    · apply Measurable.prodMk
      · apply Measurable.prodMk
        · apply Measurable.prodMk
          · fun_prop
          · exact (cache_measurable t B j).comp measurable_fst
        · fun_prop
      · exact (NumericalOrdinaryProcedure.coordinates d).symm.continuous.measurable.comp measurable_snd
    · fun_prop
  apply Measurable.prodMk
  · apply Measurable.prodMk
    · fun_prop
    · apply Measurable.prodMk
      · fun_prop
      · exact (AugmentedNumericalDriver.advance_measurable t P B fallback leaf policy hK N
          (ComparisonControllerReplay.taskDisclosed leaf j)).comp hm
  · apply Measurable.prodMk
    · fun_prop
    · exact measurable_const

theorem query_measurable : Measurable (query (d := d) (n := n) (r := r) (J := J)
    (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t) :=
  (AugmentedNumericalPreprocessor.query_measurable t).comp measurable_fst

theorem test_measurable : Measurable (test (d := d) (n := n) (r := r) (J := J)
    (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t) :=
  BoundedNumericalTest.test_contDiff.continuous.measurable.comp
    ((CensoredOracle.numericalMap (Y := EuclideanSpace ℝ (Fin d)) (E := E) (H := H)
      (m := 4096*J^2) t).continuous.measurable.comp
      ((AugmentedNumericalDriver.point_measurable t).comp
        (measurable_snd.comp (measurable_snd.comp measurable_fst))))

theorem selected_measurable : Measurable (selected (d := d) (n := n) (r := r) (J := J)
    (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t) :=
  measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk measurable_const)

theorem initial_measurable : Measurable (fun q : Pre × EuclideanSpace ℝ (Fin r) => initial t q.1 q.2) :=
  measurable_fst.prodMk (measurable_snd.prodMk measurable_const)

theorem enabled_measurable (j : Fin (4096*J^2+1)) : Measurable (enabled t leaf j : Pre → Bool) :=
  (measurable_of_countable (fun q : Bool × State (t+1) (4096*J^2+1) ell =>
    decide (q.1=false ∧ TaskState.current q.2=some leaf ∧ (q.2.completed leaf).val=j.val))).comp
    (((AugmentedNumericalDriver.finished_measurable t).comp (measurable_snd.comp measurable_snd)).prodMk
      ((AugmentedNumericalDriver.state_measurable t).comp (measurable_snd.comp measurable_snd)))

def program {K : ℝ} (hK : 0<K) (N : ℕ) (j : Fin (4096*J^2+1)) : TestSelectionMachine.Program d Run where
  mode := mode t leaf j
  think := fun s => stepReply t P B fallback leaf policy K N j s 0
  query := query t
  next := fun q => stepReply t P B fallback leaf policy K N j q.1 q.2
  test := test t
  selected := selected t
  mode_measurable := mode_measurable t leaf j
  think_measurable := (stepReply_measurable t P B fallback leaf policy hK N j).comp
    (measurable_id.prodMk measurable_const)
  query_measurable := query_measurable t
  next_measurable := stepReply_measurable t P B fallback leaf policy hK N j
  test_measurable := test_measurable t
  selected_measurable := selected_measurable t

def cappedProgram {K : ℝ} (hK : 0<K) (N : ℕ) (j : Fin (4096*J^2+1)) :
    TestSelectionMachine.Program d (Run × ℕ × ℕ) :=
  SelectionCappedProgram.cap (program t P B fallback leaf policy hK N j)

theorem capped_calls {K : ℝ} (hK : 0<K) (N : ℕ) (j : Fin (4096*J^2+1))
    (A : Matrix (Fin d) (Fin d) ℝ) (fuel q R : ℕ) (s : Run) :
    (cappedProgram t P B fallback leaf policy hK N j).queryCount A fuel (s,q,R)≤q ∧
    (cappedProgram t P B fallback leaf policy hK N j).selections A fuel (s,q,R)≤R :=
  SelectionCappedProgram.calls_le (program t P B fallback leaf policy hK N j) A s q R fuel

theorem test_norm (s : Run) : ‖test t s‖≤1 := BoundedNumericalTest.test_norm _

theorem capped_test_norm {K : ℝ} (hK : 0<K) (N : ℕ) (j : Fin (4096*J^2+1)) (s : Run × ℕ × ℕ) :
    ‖(cappedProgram t P B fallback leaf policy hK N j).test s‖≤1 := test_norm t s.1

end GradientHessian.AugmentedNumericalPostprocessor
