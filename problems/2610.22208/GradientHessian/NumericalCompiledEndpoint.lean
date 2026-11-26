import GradientHessian.NumericalSavedConfiguration
import GradientHessian.NumericalSourceCaches
import GradientHessian.NumericalCachedEarlyPhase
import GradientHessian.NumericalPreSupplyEquality
import GradientHessian.NumericalSupplySplit
import GradientHessian.NumericalPostEndpoint
import GradientHessian.NumericalPostprocessor
import GradientHessian.NumericalMaskedDriverEquality
import GradientHessian.ControllerExternalReceiptCongruence
import GradientHessian.NumericalPreloadExecution
import GradientHessian.NumericalRuleAgreement
import GradientHessian.NumericalRichAgreement
import GradientHessian.ControllerReceiptCongruence
import GradientHessian.NumericalProductStep
import GradientHessian.NumericalRuntime
import GradientHessian.NumericalOrdinaryProcedure
noncomputable section
namespace GradientHessian.NumericalCompiledEndpoint
open Matrix
open scoped InnerProductSpace
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

open NumericalCoefficientPatch CensoredOracle

open NumericalSourceCaches ControllerDriverMonotonicity ControllerDriverResource TaskSlots VisibilityTaskWindow
  ControllerNormalRealization

open scoped InnerProductSpace

theorem rawEvent_of_endpoint {K : ℝ} (hK : 0<K) (hell : 0<ell)
    (x : RawHierarchy.Raw d n r J E H t × Seed) (N : ℕ) (j : Fin (4096*J^2+1))
    (k steps rem : ℕ) (a : S) (output : Bool)
    (p : Pending (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t))
    (u : State (t+1) (4096*J^2+1) ell) :
    let w := input t leaf j x
    let A := ForkMachineBound.sourceA J P w
    let readout := ForkMachineBound.earlierReadout J P fallback w
    let saved := NumericalPreloadTransparency.savedRuntime (ell := ell) P B fallback t leaf policy K j A readout N w.1.2 k
    let branch := NumericalPostprocessor.initial t saved w.2.1
    Ready (stateOf saved.2.2) → Coherent (taskDisclosed leaf j) saved.2.2 →
    TaskState.current (stateOf saved.2.2)=some leaf →
    ((stateOf saved.2.2).completed leaf).val=j.val →
    NumericalDriverInstructions.finished saved.2.2=false →
    NumericalPostEndpoint.unguarded P B fallback t leaf policy K j A branch steps=.pending rem a output (.normal p u) →
    IsEarlyFor (rules K (RawHierarchy.assemble P B fallback t x.1)) p u (leaf,j) →
    taskDisclosed leaf j u=false →
    x∈NumericalForkProbability.rawEvent (ell := ell) P B fallback t leaf policy hK j N := by
  intro w A readout saved branch hsready hscoherent hscurrent hsindex hsfinished hres hearly hstop
  have hsupply : markSupplied leaf j (stateOf saved.2.2)=true :=
    decide_eq_true (Or.inr ⟨hscurrent,by omega⟩)
  have hshalt : NumericalPreprocessor.halt t leaf j saved=true := by
    simp [NumericalPreprocessor.halt,hsupply]
  obtain ⟨fuel,hmode,htest⟩ := NumericalPostEndpoint.selected_of_unguarded_normal P B fallback t leaf policy
    hK hell j A branch rfl hsready hscoherent hscurrent hsindex steps rem a output p u hres hearly.2.2.1 hstop
  have hcapstate := NumericalPreloadTransparency.capped_state P B fallback t leaf policy hK hell j A readout N w.1.2 k
  have hcapflag := NumericalPreloadTransparency.capped_halted P B fallback t leaf policy hK hell j A readout N w.1.2 k hshalt
  have hhit : ForkLifetime.gamma < |⟪UnmarkedReadout.sourceOutput J P w.1.1 B fallback w.2.1,
      BoundedNumericalTest.test (CensoredOracle.numericalMap t p.point)⟫_ℝ| := by
    have hh := hearly.2.2.2.1
    change hit (RawHierarchy.assemble P B fallback t x.1) u p.point=true at hh
    rw [hit_current _ u p.point hearly.1] at hh
    have hj : (⟨(u.completed leaf).val,TaskState.current_live u hearly.1⟩ : Fin (4096*J^2+1))=j :=
      Fin.ext hearly.2.1
    rw [hj] at hh
    rw [target_readout P B fallback t leaf j x]
    simpa only [ForkLifetime.gamma,markReadout,CensoredOracle.numericalMap_eq] using (of_decide_eq_true hh)
  change w∈NumericalForkProbability.forkEvent (ell := ell) P B fallback t leaf policy hK j N
  refine ⟨j.val+k,hcapflag,?_,fuel,?_,?_⟩
  · change NumericalPostprocessor.enabled t leaf j
      (((NumericalForkPrograms.pre P B fallback t leaf policy hK j).eval A readout (j.val+k)
        ((NumericalForkPrograms.preInitial (n := n) (r := r) (ell := ell) t policy j N
          ((4096*J^2+1)*ell+1) (4096*J^2+1)).1 w.1.2)).2.1.1)=true
    rw [hcapstate]
    exact decide_eq_true ⟨hsfinished,hscurrent,hsindex⟩
  · change (NumericalPostprocessor.cappedProgram P B fallback t leaf policy hK j).mode
      ((NumericalPostprocessor.cappedProgram P B fallback t leaf policy hK j).run A fuel
        (NumericalPostprocessor.initial t
          (((NumericalForkPrograms.pre P B fallback t leaf policy hK j).eval A readout (j.val+k)
            ((NumericalForkPrograms.preInitial (n := n) (r := r) (ell := ell) t policy j N
              ((4096*J^2+1)*ell+1) (4096*J^2+1)).1 w.1.2)).2.1.1) w.2.1,ell+1,ell+3))=3
    rw [hcapstate]
    exact hmode
  · change ForkLifetime.gamma < |⟪UnmarkedReadout.sourceOutput J P w.1.1 B fallback w.2.1,
      (NumericalPostprocessor.cappedProgram P B fallback t leaf policy hK j).test
        ((NumericalPostprocessor.cappedProgram P B fallback t leaf policy hK j).run A fuel
          (NumericalPostprocessor.initial t
            (((NumericalForkPrograms.pre P B fallback t leaf policy hK j).eval A readout (j.val+k)
              ((NumericalForkPrograms.preInitial (n := n) (r := r) (ell := ell) t policy j N
                ((4096*J^2+1)*ell+1) (4096*J^2+1)).1 w.1.2)).2.1.1) w.2.1,ell+1,ell+3))⟫_ℝ|
    rw [hcapstate,htest]
    exact hhit

end GradientHessian.NumericalCompiledEndpoint
