import GradientHessian.MarkRepairProbability
import GradientHessian.GeometricStoppedAction

/-! Original-policy future-mark repairs: true-jet execution, stopped-shadow
coupling, actual visibility budget, and the source product-law tail bound. -/

noncomputable section
namespace GradientHessian.MarkVisibleQueries
open Classical MeasureTheory HigherHierarchy HierarchyAddresses RawHierarchy
open FrontierState TaskState TaskSlots GeometricRepair ComparisonController ComparisonControllerReplay
open ControllerPolicyCoupling Matrix LowRank

variable {d n r J ell : ℕ} {E : Type} {H : ℕ → Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [∀ h,MeasurableSpace (H h)] [∀ h,BorelSpace (H h)] [∀ h,FiniteDimensional ℝ (H h)]
variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ)
  (t : ℕ) (leaf : Leaf (t+1)) (j : Fin (4096*J^2+1))
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
variable [NeZero r] [IsProbabilityMeasure (ConditionedSource.sourceLaw (n := n) P J)]
  (σ : Measure Seed) [IsProbabilityMeasure σ]

/-- The original true-jet policy's chronological repair event, including
its virtual output query. No shadow execution occurs in this definition. -/
def originalRepair (K : ℝ) (N : ℕ) (w : Raw d n r J E H t × Seed) : Prop :=
  Action.futureMark leaf j ∈ ControllerRepairEvents.actions
    (rules (ell := ell) K (assemble P B fallback t w.1))
    (ControllerPolicyTrace.withOutput policy
      (JetLocality.ordinaryJet (scalar K t (assemble P B fallback t w.1)))
      (JetLocality.richJet (scalar K t (assemble P B fallback t w.1))) N w.2)
    TaskState.initial

theorem originalRepair_implies_hitBy {K : ℝ} (hK : 0<K) (N : ℕ)
    (hell : 0<ell) (w : Raw d n r J E H t × Seed)
    (hd : Valid _ _ _ _ t (assemble P B fallback t w.1))
    (ha : originalRepair (ell := ell) P B fallback t leaf j policy K N w) :
    hitBy (ell := ell) P B fallback t leaf j policy K N ((N+1)*(8^(t+1)+4)) TaskState.initial w := by
  have hd' : Valid _ _ _ _ t
      (HierarchyParameters.decode t (coefficients P B fallback t w.1)) := by
    simpa only [decode_coefficients] using hd
  have ha' : Action.futureMark leaf j ∈ ControllerRepairEvents.actions
      (rules (ell := ell) K (HierarchyParameters.decode t (coefficients P B fallback t w.1)))
      (ControllerPolicyTrace.withOutput policy
        (JetLocality.ordinaryJet (scalar K t (HierarchyParameters.decode t (coefficients P B fallback t w.1))))
        (JetLocality.richJet (scalar K t (HierarchyParameters.decode t (coefficients P B fallback t w.1)))) N w.2)
      TaskState.initial := by
    simpa only [decode_coefficients] using ha
  obtain ⟨i,hi,hh⟩ := GeometricStoppedAction.future_mark_has_shadow_hit t policy hK
    (coefficients P B fallback t w.1) hd' hell N w.2 leaf j ha'
  refine ⟨i,hi.le,?_⟩
  simpa only [MarkPolicyReplay.run,MarkPolicyReplay.ordinary,MarkPolicyReplay.rich,decode_coefficients] using hh

/-- The complete actual-policy future-mark repair bound under the original
presampled objective and independent private randomness. -/
theorem original_repair_probability_bound [Nontrivial E] [∀ h,Nontrivial (H h)]
    (hJ : 4≤J) (hP : IsOrthogonalProjector P) (hB : Bᵀ*B=1) (hPB : P*B=B)
    {K : ℝ} (hK : 0<K) (N : ℕ) (hell : 0<ell) :
    ((RawHierarchy.law (n := n) (r := r) (J := J) (E := E) (H := H) P t).prod σ).real
      {w | originalRepair (ell := ell) P B fallback t leaf j policy K N w} ≤
        ((4096*J^2+1)*ell : ℕ)*(2*Real.exp (-(1/8)*(1/3072:ℝ)^2*(r:ℝ))) := by
  letI := RawHierarchy.law_probability (n := n) (r := r) (J := J) (E := E) (H := H) P t
  have hd : ∀ᵐ w : Raw d n r J E H t × Seed ∂(RawHierarchy.law P t).prod σ,
      Valid _ _ _ _ t (assemble P B fallback t w.1) :=
    Measure.quasiMeasurePreserving_fst.ae (RawHierarchy.law_assemble_valid hJ hP B hB hPB fallback t)
  have hs : ∀ᵐ w : Raw d n r J E H t × Seed ∂(RawHierarchy.law P t).prod σ,
      originalRepair (ell := ell) P B fallback t leaf j policy K N w →
        hitBy (ell := ell) P B fallback t leaf j policy K N ((N+1)*(8^(t+1)+4)) TaskState.initial w := by
    filter_upwards [hd] with w hw
    exact originalRepair_implies_hitBy (ell := ell) P B fallback t leaf j policy hK N hell w hw
  apply le_trans (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hs))
  exact shadow_hit_probability_bound (ell := ell) P B fallback t leaf j policy σ hJ hP hB hPB hK N
    ((N+1)*(8^(t+1)+4)) TaskState.initial (initial_ready hell) hell

end GradientHessian.MarkVisibleQueries