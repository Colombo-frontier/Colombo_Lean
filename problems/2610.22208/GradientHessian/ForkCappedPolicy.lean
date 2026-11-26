import GradientHessian.DisclosureCompiler
import GradientHessian.MachineSnapshot

/-! Actual post-mark machines at a deterministic cutoff. Closed marks return
zero tests. A measurable unit-ball clipping ensures validity on every
counterfactual history and preserves every valid actual test. -/

namespace GradientHessian.ForkCappedPolicy
open Matrix MeasureTheory LowRank OracleComposition
noncomputable section

def clip {d : ℕ} (y : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  if ‖y‖ ≤ 1 then y else ‖y‖⁻¹ • y

theorem clip_measurable (d : ℕ) : Measurable (@clip d) :=
  Measurable.ite (measurableSet_le measurable_norm measurable_const) measurable_id
    (measurable_norm.inv.smul measurable_id)

theorem clip_norm {d : ℕ} (y : EuclideanSpace ℝ (Fin d)) : ‖clip y‖ ≤ 1 := by
  by_cases h : ‖y‖ ≤ 1
  · simp [clip,h]
  · have hp : 0 < ‖y‖ := by linarith
    simp [clip,h,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hp),hp.ne']

theorem clip_eq {d : ℕ} {y : EuclideanSpace ℝ (Fin d)} (h : ‖y‖ ≤ 1) : clip y = y :=
  if_pos h

def clipTests {d s : ℕ} : MeasurableStateMap
    (Fin s → EuclideanSpace ℝ (Fin d)) (Fin s → EuclideanSpace ℝ (Fin d)) :=
  ⟨fun y j => clip (y j), measurable_pi_lambda _ (fun j => (clip_measurable d).comp (measurable_pi_apply j))⟩

variable {d q s : ℕ} {PreState PostState Fresh : Type*}
  [MeasurableSpace PreState] [MeasurableSpace PostState] [MeasurableSpace Fresh]

def openFlag (enabled : MeasurableStateMap PreState Bool) :
    MeasurableStateMap ((Bool × PreState) × Fresh) Bool :=
  ⟨fun t => t.1.1 && enabled.1 t.1.2,
    (show Measurable (fun b : Bool × Bool => b.1 && b.2) from measurable_of_countable _).comp
      (measurable_fst.fst.prodMk (enabled.2.comp measurable_fst.snd))⟩

def initialMap (initial : MeasurableStateMap (PreState × Fresh) PostState) :
    MeasurableStateMap ((Bool × PreState) × Fresh) PostState :=
  ⟨fun t => initial.1 (t.1.2,t.2), initial.2.comp (measurable_fst.snd.prodMk measurable_snd)⟩

def post (program : MachineCompiler.Program d PostState (Fin s → EuclideanSpace ℝ (Fin d)))
    (initial : MeasurableStateMap (PreState × Fresh) PostState)
    (enabled : MeasurableStateMap PreState Bool) (q n : ℕ) :
    Procedure d q ((Bool × PreState) × Fresh) (Fin s → EuclideanSpace ℝ (Fin d)) :=
  (Procedure.choose (openFlag enabled)
    ((program.snapshotProcedure q n).comap (initialMap initial))
    (Procedure.idle d q ⟨fun _ => 0,measurable_const⟩)).mapOutput clipTests

theorem post_norm (program : MachineCompiler.Program d PostState (Fin s → EuclideanSpace ℝ (Fin d)))
    (initial : MeasurableStateMap (PreState × Fresh) PostState)
    (enabled : MeasurableStateMap PreState Bool) (q n : ℕ)
    (A : Matrix (Fin d) (Fin d) ℝ) (state : (Bool × PreState) × Fresh) (j : Fin s) :
    ‖(post program initial enabled q n).run A state j‖ ≤ 1 :=
  clip_norm _

theorem post_closed (program : MachineCompiler.Program d PostState (Fin s → EuclideanSpace ℝ (Fin d)))
    (initial : MeasurableStateMap (PreState × Fresh) PostState)
    (enabled : MeasurableStateMap PreState Bool) (q n : ℕ)
    (A : Matrix (Fin d) (Fin d) ℝ) (state : (Bool × PreState) × Fresh)
    (hc : ¬(state.1.1 = true ∧ enabled.1 state.1.2 = true)) :
    (post program initial enabled q n).run A state = 0 := by
  simp only [post,Procedure.run_mapOutput,Procedure.run_choose,openFlag,Bool.and_eq_true]
  rw [if_neg hc,Procedure.run_idle]
  funext j
  simp [clipTests,clip]

theorem post_open (program : MachineCompiler.Program d PostState (Fin s → EuclideanSpace ℝ (Fin d)))
    (initial : MeasurableStateMap (PreState × Fresh) PostState)
    (enabled : MeasurableStateMap PreState Bool) (q n : ℕ)
    (A : Matrix (Fin d) (Fin d) ℝ) (hA : Aᵀ = A)
    (state : PreState) (fresh : Fresh) (hen : enabled.1 state = true)
    (hcap : program.calls (fun v => A*ᵥv) n (initial.1 (state,fresh)) ≤ q)
    (hnorm : ∀ j, ‖program.output ((program.step (fun v => A*ᵥv))^[n] (initial.1 (state,fresh))) j‖ ≤ 1) :
    (post program initial enabled q n).run A ((true,state),fresh) =
      program.output ((program.step (fun v => A*ᵥv))^[n] (initial.1 (state,fresh))) := by
  simp only [post,Procedure.run_mapOutput,Procedure.run_choose,openFlag,hen,Bool.true_and,if_true,
    Procedure.run_comap,initialMap]
  rw [program.run_snapshotProcedure q n A hA _ hcap]
  funext j
  exact clip_eq (hnorm j)

end
end GradientHessian.ForkCappedPolicy
