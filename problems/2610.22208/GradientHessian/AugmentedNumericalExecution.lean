import GradientHessian.AugmentedNumericalEquality
import GradientHessian.AugmentedNumericalDriver
import GradientHessian.AugmentedNumericalCursorCounts
import GradientHessian.AugmentedNumericalRuntime
import GradientHessian.NumericalMaskedDriverEquality
import GradientHessian.ControllerExternalReceiptCongruence
noncomputable section
namespace GradientHessian.AugmentedNumericalExecution
open Matrix
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
open AugmentedNumericalDriver ControllerDriverMonotonicity TaskSlots

def fullCursor (K : ℝ) (cutoff : ℕ) (stop : State (t+1) (4096*J^2+1) ell → Bool)
    (seed : Seed) (w : RawLeafFactor.Rest d n r J E H t) (c : Cache d J) (A : Matrix (Fin d) (Fin d) ℝ) :
    Cursor (d := d) (J := J) (ell := ell) (E := E) (H := H) (S := S) t →
      Cursor (d := d) (J := J) (ell := ell) (E := E) (H := H) (S := S) t :=
  AugmentedNumericalCursorCounts.step policy (NumericalShadowRules.shadowRules P B fallback t leaf K w c) stop
    (AugmentedNumericalEquality.ordinary P B fallback t leaf K w c A)
    (AugmentedNumericalReplies.rich P B fallback t leaf K w c)
    (startConfig t P B fallback leaf policy K cutoff seed w c)

theorem one_product_cursor (K : ℝ) (cutoff : ℕ) (stop : State (t+1) (4096*J^2+1) ell → Bool)
    (seed : Seed) (w : RawLeafFactor.Rest d n r J E H t) (c : Cache d J) (A : Matrix (Fin d) (Fin d) ℝ)
    (q : Cursor (d := d) (J := J) (ell := ell) (E := E) (H := H) (S := S) t) :
    AugmentedNumericalDriver.advance t P B fallback leaf policy K cutoff stop seed w c
      (if product t leaf stop q then LowRank.matrixEuclideanMap A
        (CensoredOracle.numericalMap t (point t q)) else 0) q=
      fullCursor P B fallback t leaf policy K cutoff stop seed w c A q := by
  cases q with
  | inl star => rfl
  | inr q =>
      exact congrArg Sum.inr (AugmentedNumericalEquality.one_product_step P B fallback t leaf policy K stop w c A q)

theorem active_run (K : ℝ) (cutoff : ℕ) (stop : State (t+1) (4096*J^2+1) ell → Bool)
    (seed : Seed) (w : RawLeafFactor.Rest d n r J E H t) (c : Cache d J) (A : Matrix (Fin d) (Fin d) ℝ)
    (N : ℕ) (q : Config (t+1) (4096*J^2+1) ell S (DirectionPolicyReplay.Point d J E H t) (Action t (4096*J^2))) :
    (fullCursor P B fallback t leaf policy K cutoff stop seed w c A)^[N] (.inr q)=.inr
      (ControllerPolicyDriver.run policy (NumericalShadowRules.shadowRules P B fallback t leaf K w c) stop
        (AugmentedNumericalEquality.ordinary P B fallback t leaf K w c A)
        (AugmentedNumericalReplies.rich P B fallback t leaf K w c) N q) :=
  AugmentedNumericalCursorCounts.run_active _ _ _ _ _ _ N q

theorem suspended_run (K : ℝ) (cutoff : ℕ) (stop : State (t+1) (4096*J^2+1) ell → Bool)
    (seed : Seed) (w : RawLeafFactor.Rest d n r J E H t) (c : Cache d J) (A : Matrix (Fin d) (Fin d) ℝ)
    (N : ℕ) (star : PUnit) :
    (fullCursor P B fallback t leaf policy K cutoff stop seed w c A)^[N+1] (.inl star)=.inr
      (ControllerPolicyDriver.run policy (NumericalShadowRules.shadowRules P B fallback t leaf K w c) stop
        (AugmentedNumericalEquality.ordinary P B fallback t leaf K w c A)
        (AugmentedNumericalReplies.rich P B fallback t leaf K w c) N
          (startConfig t P B fallback leaf policy K cutoff seed w c)) :=
  AugmentedNumericalCursorCounts.run_suspended_succ _ _ _ _ _ _ N star

theorem cursor_state (K : ℝ) (cutoff : ℕ) (seed : Seed)
    (w : RawLeafFactor.Rest d n r J E H t) (c : Cache d J)
    (q : Cursor (d := d) (J := J) (ell := ell) (E := E) (H := H) (S := S) t) :
    AugmentedNumericalCursorCounts.state (startConfig t P B fallback leaf policy K cutoff seed w c) q=
      state t q := by cases q <;> rfl

theorem product_lift (stop : State (t+1) (4096*J^2+1) ell → Bool)
    (q : Cursor (d := d) (J := J) (ell := ell) (E := E) (H := H) (S := S) t) :
    AugmentedNumericalCursorCounts.lift
      (fun q => if NumericalDriverInstructions.product leaf stop q then 1 else 0) q=
      if product t leaf stop q then 1 else 0 := by cases q <;> rfl

theorem product_bound (K : ℝ) (cutoff : ℕ) (stop : State (t+1) (4096*J^2+1) ell → Bool)
    (seed : Seed) (w : RawLeafFactor.Rest d n r J E H t) (c : Cache d J) (A : Matrix (Fin d) (Fin d) ℝ)
    (hell : 0<ell) (N : ℕ)
    (q : Cursor (d := d) (J := J) (ell := ell) (E := E) (H := H) (S := S) t) (hq : Ready (state t q)) :
    (∑ i∈Finset.range N,if product t leaf stop ((fullCursor P B fallback t leaf policy K cutoff stop seed w c A)^[i] q)
      then 1 else 0)≤(4096*J^2+1)*ell+1 := by
  have hh := AugmentedNumericalCursorCounts.product_bound policy
    (NumericalShadowRules.shadowRules P B fallback t leaf K w c) stop
    (AugmentedNumericalEquality.ordinary P B fallback t leaf K w c A)
    (AugmentedNumericalReplies.rich P B fallback t leaf K w c)
    (startConfig t P B fallback leaf policy K cutoff seed w c) hell leaf N q
    (by rwa [cursor_state])
  simpa only [AugmentedNumericalCursorCounts.count,AugmentedNumericalCursorCounts.run,
    product_lift,fullCursor] using hh

theorem post_product_bound (K : ℝ) (cutoff : ℕ) (j : Fin (4096*J^2+1))
    (seed : Seed) (w : RawLeafFactor.Rest d n r J E H t) (c : Cache d J) (A : Matrix (Fin d) (Fin d) ℝ)
    (hell : 0<ell) (N : ℕ)
    (q : Cursor (d := d) (J := J) (ell := ell) (E := E) (H := H) (S := S) t) (hq : Ready (state t q))
    (hcur : TaskState.current (state t q)=some leaf) (hindex : ((state t q).completed leaf).val=j.val) :
    (∑ i∈Finset.range N,if product t leaf (taskDisclosed leaf j)
      ((fullCursor P B fallback t leaf policy K cutoff (taskDisclosed leaf j) seed w c A)^[i] q)
      then 1 else 0)≤ell+1 := by
  have hh := AugmentedNumericalCursorCounts.post_product_bound policy
    (NumericalShadowRules.shadowRules P B fallback t leaf K w c)
    (AugmentedNumericalEquality.ordinary P B fallback t leaf K w c A)
    (AugmentedNumericalReplies.rich P B fallback t leaf K w c)
    (startConfig t P B fallback leaf policy K cutoff seed w c) hell leaf j N q
    (by rwa [cursor_state]) (by rwa [cursor_state]) (by rwa [cursor_state])
  simpa only [AugmentedNumericalCursorCounts.count,AugmentedNumericalCursorCounts.run,
    product_lift,fullCursor] using hh

theorem normal_lift (stop : State (t+1) (4096*J^2+1) ell → Bool)
    (q : Cursor (d := d) (J := J) (ell := ell) (E := E) (H := H) (S := S) t) :
    AugmentedNumericalCursorCounts.lift (ControllerDriverResource.normalBit (fun _ => true) stop) q=
      if normalInstruction t q && !stop (state t q) then 1 else 0 := by
  cases q with
  | inl star => rfl
  | inr q =>
      cases q with
      | ready => rfl
      | finished => rfl
      | pending n a output phase =>
          cases phase with
          | repairing => rfl
          | delivered => rfl
          | frozen => rfl
          | normal p u =>
              cases hk : p.kind <;> cases hs : stop u <;>
                simp [AugmentedNumericalCursorCounts.lift,ControllerDriverResource.normalBit,
                  normalInstruction,NumericalPostprocessor.normalInstruction,state,stateOf,phaseState,hk,hs]

theorem post_normal_bound (K : ℝ) (cutoff : ℕ) (j : Fin (4096*J^2+1))
    (seed : Seed) (w : RawLeafFactor.Rest d n r J E H t) (c : Cache d J) (A : Matrix (Fin d) (Fin d) ℝ)
    (hell : 0<ell) (N : ℕ)
    (q : Cursor (d := d) (J := J) (ell := ell) (E := E) (H := H) (S := S) t) (hq : Ready (state t q))
    (hcur : TaskState.current (state t q)=some leaf) (hindex : ((state t q).completed leaf).val=j.val) :
    (∑ i∈Finset.range N,if normalInstruction t
      ((fullCursor P B fallback t leaf policy K cutoff (taskDisclosed leaf j) seed w c A)^[i] q) &&
      !taskDisclosed leaf j (state t
        ((fullCursor P B fallback t leaf policy K cutoff (taskDisclosed leaf j) seed w c A)^[i] q))
      then 1 else 0)≤ell := by
  have hh := AugmentedNumericalCursorCounts.post_normal_bound policy
    (NumericalShadowRules.shadowRules P B fallback t leaf K w c)
    (AugmentedNumericalEquality.ordinary P B fallback t leaf K w c A)
    (AugmentedNumericalReplies.rich P B fallback t leaf K w c)
    (startConfig t P B fallback leaf policy K cutoff seed w c) hell leaf j N q
    (by rwa [cursor_state]) (by rwa [cursor_state]) (by rwa [cursor_state])
  simpa only [AugmentedNumericalCursorCounts.count,AugmentedNumericalCursorCounts.run,
    normal_lift,fullCursor] using hh

end GradientHessian.AugmentedNumericalExecution
