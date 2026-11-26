import GradientHessian.AugmentedNumericalExecution
import GradientHessian.AugmentedNumericalCaches
import GradientHessian.AugmentedNumericalRuntime
import GradientHessian.NumericalMaskedDriverEquality
import GradientHessian.ControllerExternalReceiptCongruence
noncomputable section
namespace GradientHessian.AugmentedNumericalSupplyEquality
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

open AugmentedNumericalDriver AugmentedNumericalExecution NumericalShadowRules NumericalCoefficientPatch

def externalCursor (K : ℝ) (cutoff : ℕ) (j : Fin (4096*J^2+1))
    (seed : Seed) (w : RawLeafFactor.Rest d n r J E H t) (c : Cache d J) (A : Matrix (Fin d) (Fin d) ℝ) :
    Cursor (d := d) (J := J) (ell := ell) (E := E) (H := H) (S := S) t →
      Cursor (d := d) (J := J) (ell := ell) (E := E) (H := H) (S := S) t :=
  ExternalHaltIteration.step (fullCursor P B fallback t leaf policy K cutoff (fun _ => false) seed w c A)
    (fun q => AugmentedNumericalDriver.finished t q || AugmentedDisclosure.markStop leaf j (state t q))

def externalConfig (K : ℝ) (j : Fin (4096*J^2+1))
    (w : RawLeafFactor.Rest d n r J E H t) (c : Cache d J) (A : Matrix (Fin d) (Fin d) ℝ) :=
  ControllerExternalReceiptCongruence.external policy (shadowRules P B fallback t leaf K w c)
    (AugmentedDisclosure.markStop leaf j) NumericalDriverInstructions.finished
    (AugmentedNumericalEquality.ordinary P B fallback t leaf K w c A)
    (AugmentedNumericalReplies.rich P B fallback t leaf K w c)

theorem active_step (K : ℝ) (cutoff : ℕ) (j : Fin (4096*J^2+1))
    (seed : Seed) (w : RawLeafFactor.Rest d n r J E H t) (c : Cache d J) (A : Matrix (Fin d) (Fin d) ℝ)
    (q : Config (t+1) (4096*J^2+1) ell S (DirectionPolicyReplay.Point d J E H t) (Action t (4096*J^2))) :
    externalCursor P B fallback t leaf policy K cutoff j seed w c A (.inr q)=
      .inr (externalConfig P B fallback t leaf policy K j w c A q) := by
  unfold externalCursor externalConfig ControllerExternalReceiptCongruence.external ExternalHaltIteration.step
  simp only [AugmentedNumericalDriver.finished,AugmentedNumericalDriver.state]
  change (if _ then Sum.inr q else Sum.inr _) = Sum.inr (if _ then q else _)
  split_ifs <;> rfl

theorem active_run (K : ℝ) (cutoff : ℕ) (j : Fin (4096*J^2+1))
    (seed : Seed) (w : RawLeafFactor.Rest d n r J E H t) (c : Cache d J) (A : Matrix (Fin d) (Fin d) ℝ)
    (N : ℕ) (q : Config (t+1) (4096*J^2+1) ell S (DirectionPolicyReplay.Point d J E H t) (Action t (4096*J^2))) :
    (externalCursor P B fallback t leaf policy K cutoff j seed w c A)^[N] (.inr q)=
      .inr ((externalConfig P B fallback t leaf policy K j w c A)^[N] q) := by
  induction N generalizing q with
  | zero => rfl
  | succ N ih =>
      rw [Function.iterate_succ_apply,active_step,ih,Function.iterate_succ_apply]

theorem suspended_closed (K : ℝ) (cutoff : ℕ) (j : Fin (4096*J^2+1))
    (seed : Seed) (w : RawLeafFactor.Rest d n r J E H t) (c : Cache d J) (A : Matrix (Fin d) (Fin d) ℝ)
    (hs : AugmentedDisclosure.markStop leaf j (TaskState.initial (ell := ell))=true)
    (N : ℕ) (star : PUnit) :
    (externalCursor P B fallback t leaf policy K cutoff j seed w c A)^[N] (.inl star)=.inl star := by
  have he : externalCursor P B fallback t leaf policy K cutoff j seed w c A (.inl star)=.inl star := by
    simp only [externalCursor,ExternalHaltIteration.step,AugmentedNumericalDriver.finished,state,hs,
      Bool.false_or,if_true]
  induction N with
  | zero => rfl
  | succ N ih => rw [Function.iterate_succ_apply,he,ih]

theorem suspended_open_succ (K : ℝ) (cutoff : ℕ) (j : Fin (4096*J^2+1))
    (seed : Seed) (w : RawLeafFactor.Rest d n r J E H t) (c : Cache d J) (A : Matrix (Fin d) (Fin d) ℝ)
    (hs : AugmentedDisclosure.markStop leaf j (TaskState.initial (ell := ell))=false)
    (N : ℕ) (star : PUnit) :
    (externalCursor P B fallback t leaf policy K cutoff j seed w c A)^[N+1] (.inl star)=
      .inr ((externalConfig P B fallback t leaf policy K j w c A)^[N]
        (startConfig t P B fallback leaf policy K cutoff seed w c)) := by
  have he : externalCursor P B fallback t leaf policy K cutoff j seed w c A (.inl star)=
      .inr (startConfig t P B fallback leaf policy K cutoff seed w c) := by
    simp only [externalCursor,ExternalHaltIteration.step,AugmentedNumericalDriver.finished,state,hs,
      Bool.false_or,Bool.false_eq_true,if_false]
    rfl
  rw [Function.iterate_succ_apply,he,active_run]

theorem initial_caches_eq {K : ℝ} (hK : 0<K) (hell : 0<ell)
    (x : RawHierarchy.Raw d n r J E H t) (c c' : Cache d J) (j : Fin (4096*J^2+1))
    (hb : ∀ k,k<j → c.1 k=(atLeaf t ((leafEquiv t).symm leaf) (RawHierarchy.coefficients P B fallback t x)).2.1 k)
    (ha : ∀ k,k<j → c.2 k=(atLeaf t ((leafEquiv t).symm leaf) (RawHierarchy.coefficients P B fallback t x)).2.2.1 k)
    (hb' : ∀ k,k<j → c'.1 k=(atLeaf t ((leafEquiv t).symm leaf) (RawHierarchy.coefficients P B fallback t x)).2.1 k)
    (ha' : ∀ k,k<j → c'.2 k=(atLeaf t ((leafEquiv t).symm leaf) (RawHierarchy.coefficients P B fallback t x)).2.2.1 k)
    (cutoff N : ℕ) (seed : Seed) :
    (externalCursor P B fallback t leaf policy K cutoff j seed
      (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x).2 c
      (MatrixGoodSpectrum.sourceMatrix P J (RawLeafFactor.leafNumerical t x ((leafEquiv t).symm leaf)).1))^[N]
      (.inl PUnit.unit)=
    (externalCursor P B fallback t leaf policy K cutoff j seed
      (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x).2 c'
      (MatrixGoodSpectrum.sourceMatrix P J (RawLeafFactor.leafNumerical t x ((leafEquiv t).symm leaf)).1))^[N]
      (.inl PUnit.unit) := by
  cases hs : AugmentedDisclosure.markStop leaf j (TaskState.initial (ell := ell)) with
  | true => rw [suspended_closed P B fallback t leaf policy K cutoff j seed _ c _ hs,
      suspended_closed P B fallback t leaf policy K cutoff j seed _ c' _ hs]
  | false =>
      cases N with
      | zero => rfl
      | succ N =>
          rw [suspended_open_succ P B fallback t leaf policy K cutoff j seed _ c _ hs,
            suspended_open_succ P B fallback t leaf policy K cutoff j seed _ c' _ hs]
          apply congrArg Sum.inr
          have hi := initialize_before_supply t P B fallback leaf policy K cutoff seed x c j hs hb ha
          have hi' := initialize_before_supply t P B fallback leaf policy K cutoff seed x c' j hs hb' ha'
          rw [hi,hi']
          let q0 : Config (t+1) (4096*J^2+1) ell S (DirectionPolicyReplay.Point d J E H t)
              (Action t (4096*J^2)) := ControllerPolicyDriver.initial policy cutoff
            (seed,AugmentedDisclosure.view K (RawHierarchy.assemble P B fallback t x) TaskState.initial)
            (TaskState.initial (ell := ell))
          have hc : ControllerDriverMonotonicity.Coherent (AugmentedDisclosure.markStop leaf j) q0 :=
            TaskSlots.initial_ready hell
          exact (AugmentedNumericalEquality.external_eq_source P B fallback t leaf policy hK hell x c j hb ha N
            q0 hc (by trivial)).trans
            (AugmentedNumericalEquality.external_eq_source P B fallback t leaf policy hK hell x c' j hb' ha' N
              q0 hc (by trivial)).symm

end GradientHessian.AugmentedNumericalSupplyEquality

