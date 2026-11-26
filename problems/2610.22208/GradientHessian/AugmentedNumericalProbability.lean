import GradientHessian.AugmentedNumericalForkPrograms
import GradientHessian.SelectingSourceLifetime
import GradientHessian.NumericalPreloadRuntime
import GradientHessian.NumericalPostprocessorMeasurability
import GradientHessian.SelectingFork

noncomputable section
namespace GradientHessian.AugmentedNumericalProbability
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
variable (policy : Machine.Policy (Seed × AugmentedPolicy.Packet d J E H t ell) S
  (DirectionPolicyReplay.Point d J E H t)
  (AugmentedPolicy.Ordinary d J E H t ell) (AugmentedPolicy.Rich d J E H t ell))

open Matrix MeasureTheory LowRank AugmentedNumericalForkPrograms

def forkEvent {K : ℝ} (hK : 0<K) (j : Fin (4096*J^2+1)) (N : ℕ) :
    Set (ForkMachineBound.Input d n r (RawNumericalExperiment.Auxiliary d n r J E H t Seed) PUnit.{1}) :=
  SelectingFork.selectedHit
    (pre.{_,_,1} t P B fallback leaf policy hK N j) (post t P B fallback leaf policy hK N j)
    (preInitial (n := n) (r := r) (ell := ell) t j ((4096*J^2+1)*ell+1) (4096*J^2+1))
    (postInitial (d := d) (n := n) (r := r) (J := J) (ell := ell) (E := E) (H := H)
      (Seed := Seed) (S := S) t (ell+1) (ell+3))
    (enabled (d := d) (n := n) (r := r) (ell := ell) (E := E) (H := H)
      (Seed := Seed) (S := S) t leaf j)
    J P B fallback ForkLifetime.gamma

def rawEvent {K : ℝ} (hK : 0<K) (j : Fin (4096*J^2+1)) (N : ℕ) :
    Set (RawHierarchy.Raw d n r J E H t × Seed) :=
  RawNumericalExperiment.factor t ((leafEquiv t).symm leaf) j ⁻¹'
    forkEvent (ell := ell) P B fallback t leaf policy hK j N

variable (σ : Measure Seed) [IsProbabilityMeasure σ]
variable [IsProbabilityMeasure (ConditionedSource.sourceLaw (n := n) P J)]

theorem fork_probability (κ : ℕ) (hJ : ForkLifetime.depthThreshold≤J)
    (hr : ForkLifetime.rankRatio*((4096*J^2+1:ℕ):ℝ)≤r) (hκ : 18874368≤κ)
    (hd : d=κ*r*J) (hn : n+κ*r=d)
    (hP : IsOrthogonalProjector P) (hrank : P.rank=r) (hB : Bᵀ*B=1) (hPB : P*B=B)
    (hell : ell=ForkLifetime.lifetime J) {K : ℝ} (hK : 0<K)
    (j : Fin (4096*J^2+1)) (N : ℕ) :
    (ForkMachineBound.experimentLaw (r := r) J P (gaussianMatrixLaw d n)
      (RawNumericalExperiment.auxiliaryLaw (n := n) (r := r) (J := J) (E := E) (H := H) P σ t)
      (Measure.dirac PUnit.unit)).real (forkEvent (ell := ell) P B fallback t leaf policy hK j N)≤1/256 := by
  subst ell
  apply SelectingFork.source_selection_lifetime (4096*J^2+1) J κ
    ((4096*J^2+1)*ForkLifetime.lifetime J+1) (4096*J^2+1) (ForkLifetime.lifetime J+1)
    (by omega) hJ hr hκ le_rfl le_rfl le_rfl hd hn P hP hrank B hB hPB fallback
    (pre t P B fallback leaf policy hK N j) (post t P B fallback leaf policy hK N j)
    (preInitial (n := n) (r := r) (ell := ForkLifetime.lifetime J) t j
      ((4096*J^2+1)*ForkLifetime.lifetime J+1) (4096*J^2+1))
    (postInitial (d := d) (n := n) (r := r) (J := J) (ell := ForkLifetime.lifetime J)
      (E := E) (H := H) (Seed := Seed) (S := S) t (ForkLifetime.lifetime J+1) (ForkLifetime.lifetime J+3))
    (enabled (d := d) (n := n) (r := r) (ell := ForkLifetime.lifetime J) (E := E) (H := H)
      (Seed := Seed) (S := S) t leaf j)
    (legal t P B fallback leaf policy hK j N _ _ _ _)
    (RawNumericalExperiment.auxiliaryLaw (n := n) (r := r) (J := J) (E := E) (H := H) P σ t)
    (Measure.dirac PUnit.unit)

theorem raw_probability (κ : ℕ) (hJ : ForkLifetime.depthThreshold≤J)
    (hr : ForkLifetime.rankRatio*((4096*J^2+1:ℕ):ℝ)≤r) (hκ : 18874368≤κ)
    (hd : d=κ*r*J) (hn : n+κ*r=d)
    (hP : IsOrthogonalProjector P) (hrank : P.rank=r) (hB : Bᵀ*B=1) (hPB : P*B=B)
    (hell : ell=ForkLifetime.lifetime J) {K : ℝ} (hK : 0<K)
    (j : Fin (4096*J^2+1)) (N : ℕ) :
    ((RawHierarchy.law (n := n) P t).prod σ).real (rawEvent (ell := ell) P B fallback t leaf policy hK j N)≤1/256 := by
  have he := (RawNumericalExperiment.factor_experiment_preserving
    (n := n) (r := r) (J := J) (E := E) (H := H) P σ t ((leafEquiv t).symm leaf) j).measure_preimage_equiv
      (forkEvent (ell := ell) P B fallback t leaf policy hK j N)
  change (((RawHierarchy.law P t).prod σ) (_ ⁻¹' _)).toReal≤_
  rw [he]
  exact fork_probability P B fallback t leaf policy σ κ hJ hr hκ hd hn hP hrank hB hPB hell hK j N

end GradientHessian.AugmentedNumericalProbability
