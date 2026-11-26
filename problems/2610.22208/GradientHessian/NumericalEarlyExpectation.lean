import GradientHessian.NumericalForkProbability
import GradientHessian.PolicyEarlyExpectation
import GradientHessian.GeometricPolicyProbability
import GradientHessian.NumericalForkPrograms
import GradientHessian.SelectingSourceLifetime
import GradientHessian.NumericalPreloadRuntime
import GradientHessian.NumericalPostprocessorMeasurability
import GradientHessian.SelectingFork

noncomputable section
namespace GradientHessian.NumericalEarlyExpectation
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

open Matrix MeasureTheory LowRank JetLocality

def earlyEvent (K : ℝ) (N : ℕ) (j : Fin (4096*J^2+1)) :
    Set (RawHierarchy.Raw d n r J E H t × Seed) :=
  PolicyEarlyExpectation.event (priority t (4096*J^2)) target
    (fun x => trigger (ell := ell) K (RawHierarchy.assemble P B fallback t x))
    (fun x => hit (ell := ell) (RawHierarchy.assemble P B fallback t x)) policy
    (fun x => ordinaryJet (scalar K t (RawHierarchy.assemble P B fallback t x)))
    (fun x => richJet (scalar K t (RawHierarchy.assemble P B fallback t x))) N (leaf,j)

variable (σ : Measure Seed) [IsProbabilityMeasure σ]
variable [IsProbabilityMeasure (ConditionedSource.sourceLaw (n := n) P J)]

theorem early_probability_of_containment (κ : ℕ) (hJ : ForkLifetime.depthThreshold≤J)
    (hr : ForkLifetime.rankRatio*((4096*J^2+1:ℕ):ℝ)≤r) (hκ : 18874368≤κ)
    (hd : d=κ*r*J) (hn : n+κ*r=d)
    (hP : IsOrthogonalProjector P) (hrank : P.rank=r) (hB : Bᵀ*B=1) (hPB : P*B=B)
    (hell : ell=ForkLifetime.lifetime J) {K : ℝ} (hK : 0<K)
    (j : Fin (4096*J^2+1)) (N : ℕ)
    (hcontain : ∀ᵐ w ∂(RawHierarchy.law (n := n) P t).prod σ,
      w∈earlyEvent (ell := ell) P B fallback t leaf policy K N j →
      w∈NumericalForkProbability.rawEvent (ell := ell) P B fallback t leaf policy hK j N) :
    ((RawHierarchy.law (n := n) P t).prod σ).real
      (earlyEvent (ell := ell) P B fallback t leaf policy K N j)≤1/256 := by
  letI := RawHierarchy.law_probability (n := n) (r := r) (J := J) (E := E) (H := H) P t
  have hm := measure_mono_ae hcontain
  have hm' := ENNReal.toReal_mono (measure_ne_top _ _) hm
  exact hm'.trans (NumericalForkProbability.raw_probability P B fallback t leaf policy σ κ
    hJ hr hκ hd hn hP hrank hB hPB hell hK j N)

theorem early_mean_of_containment (κ : ℕ) (hJ : ForkLifetime.depthThreshold≤J)
    (hr : ForkLifetime.rankRatio*((4096*J^2+1:ℕ):ℝ)≤r) (hκ : 18874368≤κ)
    (hd : d=κ*r*J) (hn : n+κ*r=d)
    (hP : IsOrthogonalProjector P) (hrank : P.rank=r) (hB : Bᵀ*B=1) (hPB : P*B=B)
    (hell : ell=ForkLifetime.lifetime J) (hellpos : 0<ell) {K : ℝ} (hK : 0<K) (N : ℕ)
    (hcontain : ∀ (leaf : Leaf (t+1)) (j : Fin (4096*J^2+1)),
      ∀ᵐ w ∂(RawHierarchy.law (n := n) P t).prod σ,
      w∈earlyEvent (ell := ell) P B fallback t leaf policy K N j →
      w∈NumericalForkProbability.rawEvent (ell := ell) P B fallback t leaf policy hK j N) :
    (∫ w,(GeometricPolicyProbability.earlyCount (ell := ell) K
      (RawHierarchy.assemble P B fallback t) policy
      (fun x => ordinaryJet (scalar K t (RawHierarchy.assemble P B fallback t x)))
      (fun x => richJet (scalar K t (RawHierarchy.assemble P B fallback t x))) N w : ℝ)
      ∂(RawHierarchy.law (n := n) P t).prod σ)≤(8:ℝ)^(t+1)*(4096*J^2+1)/256 := by
  letI := RawHierarchy.law_probability (n := n) (r := r) (J := J) (E := E) (H := H) P t
  have htr := GeometricRepair.projected_trigger_measurable (ell := ell) P B fallback t K
    (id : RawHierarchy.Raw d n r J E H t → _) measurable_id
  have hhi := GeometricRepair.projected_hit_measurable (ell := ell) P B fallback t
    (id : RawHierarchy.Raw d n r J E H t → _) measurable_id
  have ho : Measurable (fun q : RawHierarchy.Raw d n r J E H t × Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t =>
      ordinaryJet (scalar K t (RawHierarchy.assemble P B fallback t q.1)) q.2) :=
    (RawHierarchy.ordinaryJet_joint_measurable (n := n) (J := J) (E := E) (H := H) P B fallback hK t).mono
      le_rfl (le_of_eq BorelSpace.measurable_eq)
  have hv : Measurable (fun q : RawHierarchy.Raw d n r J E H t × Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t =>
      richJet (scalar K t (RawHierarchy.assemble P B fallback t q.1)) q.2) :=
    (RawHierarchy.richJet_joint_measurable (n := n) (J := J) (E := E) (H := H) P B fallback hK t).mono
      le_rfl (le_of_eq BorelSpace.measurable_eq)
  have hm := PolicyEarlyExpectation.mean_le_inventory_fraction (priority t (4096*J^2)) target
    (fun x => trigger (ell := ell) K (RawHierarchy.assemble P B fallback t x))
    (fun x => hit (ell := ell) (RawHierarchy.assemble P B fallback t x)) htr hhi policy
    (fun x => ordinaryJet (scalar K t (RawHierarchy.assemble P B fallback t x)))
    (fun x => richJet (scalar K t (RawHierarchy.assemble P B fallback t x))) ho hv
    ((RawHierarchy.law (n := n) P t).prod σ) N hellpos
    (fun q => early_probability_of_containment P B fallback t q.1 policy σ κ hJ hr hκ hd hn
      hP hrank hB hPB hell hK q.2 N (hcontain q.1 q.2))
  simpa only [GeometricPolicyProbability.earlyCount,PolicyEarlyIntegrability.count,
    PolicyRepairExpectation.policyRules,ControllerMeasurable.parameterRules,GeometricRepair.rules,
    Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one] using hm

end GradientHessian.NumericalEarlyExpectation
