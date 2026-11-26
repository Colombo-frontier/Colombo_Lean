import GradientHessian.NumericalPreloadRuntime
import GradientHessian.NumericalPostprocessorMeasurability
import GradientHessian.SelectingFork

noncomputable section
namespace GradientHessian.NumericalForkPrograms
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

open NumericalPreprocessor LowRank

abbrev PreState := (RuntimeState (d := d) (n := n) (r := r) (J := J)
  (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t × ℕ) × ℕ × ℕ

abbrev PostState := NumericalPostprocessor.RuntimeState (d := d) (n := n) (r := r) (J := J)
  (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t × ℕ × ℕ

def pre {K : ℝ} (hK : 0<K) (j : Fin (4096*J^2+1)) :
    DisclosureCompiler.Program d (PreState (d := d) (n := n) (r := r) (J := J)
      (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t) :=
  DisclosureCappedProgram.cap (NumericalPreloadRuntime.program P B fallback t leaf policy hK j)

def post {K : ℝ} (hK : 0<K) (j : Fin (4096*J^2+1)) :
    TestSelectionMachine.Program d (PostState (d := d) (n := n) (r := r) (J := J)
      (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t) :=
  NumericalPostprocessor.cappedProgram P B fallback t leaf policy hK j

def preInitial (j : Fin (4096*J^2+1)) (N q R : ℕ) :
    MeasurableStateMap (RawNumericalExperiment.Auxiliary d n r J E H t Seed)
      (PreState (d := d) (n := n) (r := r) (J := J) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t) :=
  ⟨fun w => ((NumericalPreprocessor.initial t policy N w,j.val),q,R),
    ((NumericalPreprocessor.initial_measurable (n := n) (r := r) (ell := ell) t policy N).prodMk measurable_const).prodMk
      (measurable_const.prodMk measurable_const)⟩

def postInitial (q R : ℕ) :
    MeasurableStateMap ((PreState (d := d) (n := n) (r := r) (J := J)
      (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t) × (EuclideanSpace ℝ (Fin r) × PUnit))
      (PostState (d := d) (n := n) (r := r) (J := J) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t) :=
  ⟨fun w => (NumericalPostprocessor.initial t w.1.1.1 w.2.1,q,R),
    ((NumericalPostprocessor.initial_measurable t).comp
      ((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
        (measurable_fst.comp measurable_snd))).prodMk (measurable_const.prodMk measurable_const)⟩

def enabled (j : Fin (4096*J^2+1)) :
    MeasurableStateMap (PreState (d := d) (n := n) (r := r) (J := J)
      (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t) Bool :=
  ⟨fun w => NumericalPostprocessor.enabled t leaf j w.1.1,
    (NumericalPostprocessor.enabled_measurable t leaf j).comp (measurable_fst.comp measurable_fst)⟩

theorem legal {K : ℝ} (hK : 0<K) (j : Fin (4096*J^2+1)) (N q₀ R q₁ s : ℕ) :
    SelectingFork.LegalSelections (n := n)
      (pre P B fallback t leaf policy hK j) (post P B fallback t leaf policy hK j)
      (preInitial (n := n) (r := r) (ell := ell) t policy j N q₀ R)
      (postInitial (d := d) (n := n) (r := r) (J := J) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t q₁ s)
      (enabled (d := d) (n := n) (r := r) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t leaf j)
      J P fallback q₀ R q₁ s := by
  constructor
  · intro w _ nsteps
    exact DisclosureCappedProgram.calls_le (NumericalPreloadRuntime.program P B fallback t leaf policy hK j)
      (ForkMachineBound.sourceA J P w) (ForkMachineBound.earlierReadout J P fallback w) nsteps
      (NumericalPreprocessor.initial t policy N w.1.2,j.val) q₀ R
  · intro w _ _ cut _ _ nsteps
    have hc := NumericalPostprocessor.capped_calls P B fallback t leaf policy hK j
      (ForkMachineBound.sourceA J P w) nsteps q₁ s
      (NumericalPostprocessor.initial t
        (ForkMachineBound.saved (pre P B fallback t leaf policy hK j) J P fallback
          (preInitial (n := n) (r := r) (ell := ell) t policy j N q₀ R) cut w).2.1.1 w.2.1)
    refine ⟨hc.1,hc.2,?_⟩
    intro _
    exact NumericalPostprocessor.capped_test_norm P B fallback t leaf policy hK j _

end GradientHessian.NumericalForkPrograms