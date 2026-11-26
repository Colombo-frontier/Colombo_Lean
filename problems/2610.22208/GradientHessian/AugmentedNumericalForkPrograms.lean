import GradientHessian.AugmentedNumericalPostprocessor
import GradientHessian.SelectingFork

/-! A genuine selecting fork for the augmented oracle. Public initialization
is suspended in preprocessing, and the fresh target mark is installed before
the postprocessor can initialize the policy. Both resource caps are total. -/

noncomputable section
namespace GradientHessian.AugmentedNumericalForkPrograms
open Classical HigherHierarchy HierarchyAddresses FrontierState TaskState LowRank

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

abbrev PreState := (AugmentedNumericalPreprocessor.RuntimeState (d := d) (n := n) (r := r)
  (J := J) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t × ℕ) × ℕ × ℕ
abbrev PostState := AugmentedNumericalPostprocessor.RuntimeState (d := d) (n := n) (r := r)
  (J := J) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t × ℕ × ℕ
local notation "Pre" => PreState (d := d) (n := n) (r := r) (J := J) (ell := ell)
  (E := E) (H := H) (Seed := Seed) (S := S) t
local notation "Post" => PostState (d := d) (n := n) (r := r) (J := J) (ell := ell)
  (E := E) (H := H) (Seed := Seed) (S := S) t

variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ)
  (leaf : Leaf (t+1))
  (policy : Machine.Policy (Seed × AugmentedPolicy.Packet d J E H t ell) S
    (DirectionPolicyReplay.Point d J E H t)
    (AugmentedPolicy.Ordinary d J E H t ell) (AugmentedPolicy.Rich d J E H t ell))

def pre {K : ℝ} (hK : 0<K) (N : ℕ) (j : Fin (4096*J^2+1)) : DisclosureCompiler.Program d Pre :=
  AugmentedNumericalPreprocessor.cappedProgram t P B fallback leaf policy hK N j

def post {K : ℝ} (hK : 0<K) (N : ℕ) (j : Fin (4096*J^2+1)) : TestSelectionMachine.Program d Post :=
  AugmentedNumericalPostprocessor.cappedProgram t P B fallback leaf policy hK N j

def preInitial (j : Fin (4096*J^2+1)) (q R : ℕ) :
    MeasurableStateMap (RawNumericalExperiment.Auxiliary d n r J E H t Seed) Pre :=
  ⟨fun w => ((AugmentedNumericalPreprocessor.initial t w,j.val),q,R),
    ((AugmentedNumericalPreprocessor.initial_measurable (d := d) (n := n) (r := r) (J := J)
      (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t).prodMk measurable_const).prodMk
      (measurable_const.prodMk measurable_const)⟩

def postInitial (q R : ℕ) : MeasurableStateMap (Pre × (EuclideanSpace ℝ (Fin r) × PUnit)) Post :=
  ⟨fun w => (AugmentedNumericalPostprocessor.initial t w.1.1.1 w.2.1,q,R),
    ((AugmentedNumericalPostprocessor.initial_measurable t).comp
      ((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
        (measurable_fst.comp measurable_snd))).prodMk (measurable_const.prodMk measurable_const)⟩

def enabled (j : Fin (4096*J^2+1)) : MeasurableStateMap Pre Bool :=
  ⟨fun w => AugmentedNumericalPostprocessor.enabled t leaf j w.1.1,
    (AugmentedNumericalPostprocessor.enabled_measurable t leaf j).comp (measurable_fst.comp measurable_fst)⟩

theorem legal {K : ℝ} (hK : 0<K) (j : Fin (4096*J^2+1)) (N q₀ R q₁ s : ℕ) :
    SelectingFork.LegalSelections (n := n)
      (pre t P B fallback leaf policy hK N j) (post t P B fallback leaf policy hK N j)
      (preInitial (d := d) (n := n) (r := r) (J := J) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t j q₀ R)
      (postInitial (d := d) (n := n) (r := r) (J := J) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t q₁ s)
      (enabled (d := d) (n := n) (r := r) (J := J) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t leaf j)
      J P fallback q₀ R q₁ s := by
  constructor
  · intro w _ nsteps
    exact AugmentedNumericalPreprocessor.capped_calls t P B fallback leaf policy hK N j
      (ForkMachineBound.sourceA J P w) (ForkMachineBound.earlierReadout J P fallback w) nsteps q₀ R
      (AugmentedNumericalPreprocessor.initial t w.1.2,j.val)
  · intro w _ _ cut _ _ nsteps
    have hc := AugmentedNumericalPostprocessor.capped_calls t P B fallback leaf policy hK N j
      (ForkMachineBound.sourceA J P w) nsteps q₁ s
      (AugmentedNumericalPostprocessor.initial t
        (ForkMachineBound.saved (pre t P B fallback leaf policy hK N j) J P fallback
          (preInitial (d := d) (n := n) (r := r) (J := J) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t j q₀ R) cut w).2.1.1 w.2.1)
    refine ⟨hc.1,hc.2,?_⟩
    intro _
    exact AugmentedNumericalPostprocessor.capped_test_norm t P B fallback leaf policy hK N j _

end GradientHessian.AugmentedNumericalForkPrograms
