import GradientHessian.NumericalPostprocessor
import GradientHessian.NumericalPreprocessorMeasurability
import GradientHessian.SelectionCappedProgram

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

theorem cache_measurable (j : Fin (4096*J^2+1)) :
    Measurable (cache (n := n) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) B t j) := by
  apply Measurable.prodMk
  · have hm : Measurable (fun s : RuntimeState (d := d) (n := n) (r := r) (J := J)
        (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t =>
        (NumericalPreprocessor.forcing B j s.1.1.1,InverseGate.H₀ • LowRank.matrixEuclideanMap B s.2.1)) := by
      apply Measurable.prodMk
      · exact (NumericalPreprocessor.forcing_measurable B j).comp
          (measurable_fst.comp (measurable_fst.comp measurable_fst))
      · exact measurable_const.smul ((LowRank.matrixEuclideanMap B).continuous.measurable.comp
          (measurable_fst.comp measurable_snd))
    have hh := (measurable_update' (a := j)).comp hm
    simpa only [Function.comp_def] using hh
  · fun_prop

theorem halt_measurable (j : Fin (4096*J^2+1)) :
    Measurable (halt (d := d) (n := n) (r := r) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t leaf j) :=
  (measurable_of_countable (fun q : Bool × Bool => q.1 || q.2)).comp
    ((NumericalDriverInstructions.finished_measurable.comp
      (measurable_snd.comp (measurable_snd.comp measurable_fst))).prodMk
      ((measurable_of_countable (taskDisclosed leaf j)).comp
        (NumericalDriverInstructions.stateOf_measurable.comp
          (measurable_snd.comp (measurable_snd.comp measurable_fst)))))

theorem normalInstruction_measurable :
    Measurable (normalInstruction (d := d) (J := J) (ell := ell) (E := E) (H := H) (S := S) t) := by
  have hh : Measurable (fun q : Unit × Config (t+1) (4096*J^2+1) ell S
      (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) (Action t (4096*J^2)) => normalInstruction t q.2) := by
    apply measurable_config_cases (fun (_ : Unit) q => normalInstruction t q)
    · exact measurable_const
    · have hp : Measurable (fun q : Unit × PendingData (t+1) (4096*J^2+1) ell S
          (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) (Action t (4096*J^2)) =>
          phaseEquiv (t+1) (4096*J^2+1) ell _ _ q.2.2.2.2) :=
        (phaseMeasurableEquiv _ _ _ _ _).measurable.comp
          (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
      let f : Kind × PhaseData (t+1) (4096*J^2+1) ell → Bool := fun z => match z.2 with
        | .inr (.inl _) => decide (z.1=.ordinary)
        | _ => false
      have hh := (measurable_of_countable f).comp
        ((measurable_pending_kind.comp (measurable_fst.comp hp)).prodMk (measurable_snd.comp hp))
      convert hh using 1
      funext q
      rcases q with ⟨u,N,a,o,phase⟩
      cases phase <;> rfl
    · exact measurable_const
  exact hh.comp ((measurable_const (a := ())).prodMk measurable_id)

theorem mode_measurable (j : Fin (4096*J^2+1)) :
    Measurable (mode (d := d) (n := n) (r := r) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t leaf j) := by
  have hm : Measurable (fun s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
      (E := E) (H := H) (Seed := Seed) (S := S) t =>
      (halt t leaf j s,normalInstruction t s.1.2.2,s.2.2,
        NumericalDriverInstructions.product leaf (taskDisclosed leaf j) s.1.2.2)) :=
    (halt_measurable t leaf j).prodMk
      (((normalInstruction_measurable t).comp (measurable_snd.comp (measurable_snd.comp measurable_fst))).prodMk
        ((measurable_snd.comp measurable_snd).prodMk
          ((NumericalDriverInstructions.product_measurable leaf (taskDisclosed leaf j)).comp
            (measurable_snd.comp (measurable_snd.comp measurable_fst)))))
  have hh := (measurable_of_countable (fun z : Bool × Bool × Bool × Bool =>
    if z.1 then (0 : Fin 4) else if z.2.1 && !z.2.2.1 then 3 else if z.2.2.2 then 2 else 1)).comp hm
  simpa only [Function.comp_def,mode] using hh

theorem stepReply_measurable {K : ℝ} (hK : 0<K) (j : Fin (4096*J^2+1)) :
    Measurable (fun q : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
      (E := E) (H := H) (Seed := Seed) (S := S) t × (Fin d → ℝ) =>
      stepReply P B fallback t leaf policy K j q.1 q.2) := by
  have hm : Measurable (fun q : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
      (E := E) (H := H) (Seed := Seed) (S := S) t × (Fin d → ℝ) =>
      (((q.1.1.1.2.1,cache B t j q.1),(NumericalOrdinaryProcedure.coordinates d).symm q.2),q.1.1.2.2)) := by
    apply Measurable.prodMk
    · apply Measurable.prodMk
      · apply Measurable.prodMk
        · fun_prop
        · exact (cache_measurable (n := n) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) B t j).comp measurable_fst
      · exact (NumericalOrdinaryProcedure.coordinates d).symm.continuous.measurable.comp measurable_snd
    · fun_prop
  have hr := (NumericalRuntime.advance_measurable (n := n) P B fallback t leaf policy hK (taskDisclosed leaf j)).comp hm
  apply Measurable.prodMk
  · apply Measurable.prodMk
    · fun_prop
    · apply Measurable.prodMk
      · fun_prop
      · exact hr
  · exact (measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk measurable_const

theorem query_measurable :
    Measurable (query (d := d) (n := n) (r := r) (J := J) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t) :=
  (NumericalPreprocessor.query_measurable t).comp measurable_fst

theorem test_measurable :
    Measurable (test (d := d) (n := n) (r := r) (J := J) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t) :=
  BoundedNumericalTest.test_contDiff.continuous.measurable.comp
    ((CensoredOracle.numericalMap (Y := EuclideanSpace ℝ (Fin d)) (E := E) (H := H) (m := 4096*J^2) t).continuous.measurable.comp
      (NumericalDriverInstructions.point_measurable.comp (measurable_snd.comp (measurable_snd.comp measurable_fst))))

theorem selected_measurable :
    Measurable (selected (d := d) (n := n) (r := r) (J := J) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t) :=
  measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk measurable_const)

theorem initial_measurable :
    Measurable (fun q : NumericalPreprocessor.RuntimeState (d := d) (n := n) (r := r) (J := J)
      (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t × EuclideanSpace ℝ (Fin r) => initial t q.1 q.2) :=
  measurable_fst.prodMk (measurable_snd.prodMk measurable_const)

theorem enabled_measurable (j : Fin (4096*J^2+1)) :
    Measurable (enabled (d := d) (n := n) (r := r) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t leaf j) := by
  have hm : Measurable (fun s : NumericalPreprocessor.RuntimeState (d := d) (n := n) (r := r) (J := J)
      (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t =>
      (NumericalDriverInstructions.finished s.2.2,ControllerDriverMonotonicity.stateOf s.2.2)) :=
    (NumericalDriverInstructions.finished_measurable.comp (measurable_snd.comp measurable_snd)).prodMk
      (NumericalDriverInstructions.stateOf_measurable.comp (measurable_snd.comp measurable_snd))
  have hh := (measurable_of_countable (fun z : Bool × State (t+1) (4096*J^2+1) ell =>
    decide (z.1=false ∧ TaskState.current z.2=some leaf ∧ (z.2.completed leaf).val=j.val))).comp hm
  simpa only [Function.comp_def,enabled] using hh

def program {K : ℝ} (hK : 0<K) (j : Fin (4096*J^2+1)) :
    TestSelectionMachine.Program d (RuntimeState (d := d) (n := n) (r := r) (J := J)
      (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t) where
  mode := mode t leaf j
  think := fun s => stepReply P B fallback t leaf policy K j s 0
  query := query t
  next := fun q => stepReply P B fallback t leaf policy K j q.1 q.2
  test := test t
  selected := selected t
  mode_measurable := mode_measurable t leaf j
  think_measurable := (stepReply_measurable P B fallback t leaf policy hK j).comp
    (measurable_id.prodMk measurable_const)
  query_measurable := query_measurable t
  next_measurable := stepReply_measurable P B fallback t leaf policy hK j
  test_measurable := test_measurable t
  selected_measurable := selected_measurable t

def cappedProgram {K : ℝ} (hK : 0<K) (j : Fin (4096*J^2+1)) :
    TestSelectionMachine.Program d ((RuntimeState (d := d) (n := n) (r := r) (J := J)
      (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t) × ℕ × ℕ) :=
  SelectionCappedProgram.cap (program P B fallback t leaf policy hK j)

theorem capped_calls {K : ℝ} (hK : 0<K) (j : Fin (4096*J^2+1))
    (A : Matrix (Fin d) (Fin d) ℝ) (N q R : ℕ)
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J)
      (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t) :
    (cappedProgram P B fallback t leaf policy hK j).queryCount A N (s,q,R) ≤ q ∧
    (cappedProgram P B fallback t leaf policy hK j).selections A N (s,q,R) ≤ R :=
  SelectionCappedProgram.calls_le (program P B fallback t leaf policy hK j) A s q R N

theorem capped_test_norm {K : ℝ} (hK : 0<K) (j : Fin (4096*J^2+1))
    (s : (RuntimeState (d := d) (n := n) (r := r) (J := J)
      (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t) × ℕ × ℕ) :
    ‖(cappedProgram P B fallback t leaf policy hK j).test s‖ ≤ 1 := test_norm t s.1

end GradientHessian.NumericalPostprocessor
