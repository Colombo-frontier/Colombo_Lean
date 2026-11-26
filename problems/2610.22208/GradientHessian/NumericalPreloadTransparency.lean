import GradientHessian.NumericalPreloadBounds
import GradientHessian.NumericalForkPrograms
import GradientHessian.ExternalHaltIteration
import GradientHessian.DisclosureCapTransparency
import GradientHessian.NumericalProductStep
import GradientHessian.DisclosureIteration
import GradientHessian.ControllerDriverTaskBounds
noncomputable section
namespace GradientHessian.NumericalPreloadTransparency
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

open Matrix NumericalPreprocessor NumericalPreloadRuntime

open NumericalPreloadExecution ControllerDriverMonotonicity ControllerDriverResource TaskSlots

open NumericalPreloadBounds

def loaded (j : Fin (4096*J^2+1)) (readout : (Fin d → ℝ) → Fin d → ℝ)
    (cutoff : ℕ) (w : RawNumericalExperiment.Auxiliary d n r J E H t Seed) :
    RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
      (E := E) (H := H) (Seed := Seed) (S := S) t :=
  (w,NumericalPriorCache.store B j readout w.1,ControllerPolicyDriver.initial policy cutoff w.2.2 TaskState.initial)

def savedRuntime (K : ℝ) (j : Fin (4096*J^2+1)) (A : Matrix (Fin d) (Fin d) ℝ)
    (readout : (Fin d → ℝ) → Fin d → ℝ) (cutoff : ℕ)
    (w : RawNumericalExperiment.Auxiliary d n r J E H t Seed) (N : ℕ) :
    RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
      (E := E) (H := H) (Seed := Seed) (S := S) t :=
  (w,NumericalPriorCache.store B j readout w.1,
    (externalStep P B fallback t leaf policy K j w.2.1 (cache B t j (loaded (ell := ell) B t policy j readout cutoff w)) A)^[N]
      (ControllerPolicyDriver.initial policy cutoff w.2.2 TaskState.initial))

theorem uncapped_eval {K : ℝ} (hK : 0<K) (j : Fin (4096*J^2+1))
    (A : Matrix (Fin d) (Fin d) ℝ) (readout : (Fin d → ℝ) → Fin d → ℝ)
    (cutoff : ℕ) (w : RawNumericalExperiment.Auxiliary d n r J E H t Seed) (N : ℕ) :
    (NumericalPreloadRuntime.program P B fallback t leaf policy hK j).eval A readout (j.val+N)
      (NumericalPreprocessor.initial (ell := ell) t policy cutoff w,j.val)=
      (((baseProgram (ell := ell) P B fallback t leaf policy hK j).eval A readout N (loaded (ell := ell) B t policy j readout cutoff w)).1,
        savedRuntime (ell := ell) P B fallback t leaf policy K j A readout cutoff w N,0) := by
  have he := DisclosurePreload.eval_prepared (baseProgram (ell := ell) P B fallback t leaf policy hK j)
    (mark B t j) (write t) (mark_measurable B t j) (write_measurable t) A readout j.val N
      (NumericalPreprocessor.initial (ell := ell) t policy cutoff w)
  rw [prepared_initial B t policy j readout cutoff w] at he
  change (NumericalPreloadRuntime.program P B fallback t leaf policy hK j).eval A readout (j.val+N)
    (NumericalPreprocessor.initial (ell := ell) t policy cutoff w,j.val)=_ at he
  rw [he,base_eval_state]
  rfl

theorem uncapped_halted {K : ℝ} (hK : 0<K) (j : Fin (4096*J^2+1))
    (A : Matrix (Fin d) (Fin d) ℝ) (readout : (Fin d → ℝ) → Fin d → ℝ)
    (cutoff : ℕ) (w : RawNumericalExperiment.Auxiliary d n r J E H t Seed) (N : ℕ)
    (hh : NumericalPreprocessor.halt t leaf j (savedRuntime (ell := ell) P B fallback t leaf policy K j A readout cutoff w N)=true) :
    ((NumericalPreloadRuntime.program P B fallback t leaf policy hK j).eval A readout (j.val+N)
      (NumericalPreprocessor.initial (ell := ell) t policy cutoff w,j.val)).1=true := by
  rw [uncapped_eval]
  change ((baseProgram (ell := ell) P B fallback t leaf policy hK j).eval A readout N (loaded (ell := ell) B t policy j readout cutoff w)).1=true
  rw [DisclosureCompiler.Program.eval_flag_iterate,base_iterate]
  change (baseProgram (ell := ell) P B fallback t leaf policy hK j).mode (savedRuntime (ell := ell) P B fallback t leaf policy K j A readout cutoff w N)=0
  simp [baseProgram,hh]

theorem capped_state {K : ℝ} (hK : 0<K) (hell : 0<ell) (j : Fin (4096*J^2+1))
    (A : Matrix (Fin d) (Fin d) ℝ) (readout : (Fin d → ℝ) → Fin d → ℝ)
    (cutoff : ℕ) (w : RawNumericalExperiment.Auxiliary d n r J E H t Seed) (N : ℕ) :
    ((NumericalForkPrograms.pre P B fallback t leaf policy hK j).eval A readout (j.val+N)
      ((NumericalForkPrograms.preInitial (n := n) (r := r) (ell := ell) t policy j cutoff
        ((4096*J^2+1)*ell+1) (4096*J^2+1)).1 w)).2.1=
      (savedRuntime (ell := ell) P B fallback t leaf policy K j A readout cutoff w N,0) := by
  rw [NumericalForkPrograms.pre,NumericalForkPrograms.preInitial]
  rw [capped_preload_projects P B fallback t leaf policy hK hell j A readout
    (NumericalPreprocessor.initial (ell := ell) t policy cutoff w) (initial_ready hell) N,
    uncapped_eval]

theorem capped_halted {K : ℝ} (hK : 0<K) (hell : 0<ell) (j : Fin (4096*J^2+1))
    (A : Matrix (Fin d) (Fin d) ℝ) (readout : (Fin d → ℝ) → Fin d → ℝ)
    (cutoff : ℕ) (w : RawNumericalExperiment.Auxiliary d n r J E H t Seed) (N : ℕ)
    (hh : NumericalPreprocessor.halt t leaf j (savedRuntime (ell := ell) P B fallback t leaf policy K j A readout cutoff w N)=true) :
    ((NumericalForkPrograms.pre P B fallback t leaf policy hK j).eval A readout (j.val+N)
      ((NumericalForkPrograms.preInitial (n := n) (r := r) (ell := ell) t policy j cutoff
        ((4096*J^2+1)*ell+1) (4096*J^2+1)).1 w)).1=true := by
  exact capped_preload_halted P B fallback t leaf policy hK hell j A readout
    (NumericalPreprocessor.initial (ell := ell) t policy cutoff w) (initial_ready hell) N
      (uncapped_halted P B fallback t leaf policy hK j A readout cutoff w N hh)

end GradientHessian.NumericalPreloadTransparency

