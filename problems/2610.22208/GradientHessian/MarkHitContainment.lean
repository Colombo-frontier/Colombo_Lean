import GradientHessian.MarkVisibleQueries

/-! An actual future-mark trigger in the suppressed chronological policy
is witnessed by one entry of the independent normalized visible array. -/

noncomputable section
namespace GradientHessian.MarkVisibleQueries
open Classical HigherHierarchy HierarchyAddresses RawHierarchy
open FrontierState TaskState TaskSlots GeometricRepair ComparisonController ComparisonControllerReplay
open ControllerPolicyCoupling
open scoped InnerProductSpace

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

def hitBy (K : ℝ) (N fuel : ℕ) (s₀ : State (t+1) (4096*J^2+1) ell)
    (w : Raw d n r J E H t × Seed) : Prop :=
  ∃ i≤fuel,BlockedHit (rules K (assemble P B fallback t w.1)) (blockMark leaf j) (markSupplied leaf j)
    (MarkPolicyReplay.run P B fallback t leaf j policy K w.1 i
      (ControllerPolicyDriver.initial policy N w.2 s₀))

def arrayHit (K : ℝ) (N fuel : ℕ) (s₀ : State (t+1) (4096*J^2+1) ell)
    (w : Raw d n r J E H t × Seed) : Prop :=
  ∃ i : Fin ((4096*J^2+1)*ell),1/3072 <
    |⟪UnmarkedReadout.sourceOutput J P (RawMarkFactor.factor t ((leafEquiv t).symm leaf) j w.1).2.1 B fallback
      (RawMarkFactor.factor t ((leafEquiv t).symm leaf) j w.1).1,
      query P B fallback t leaf j policy K N fuel s₀
        ((RawMarkFactor.factor t ((leafEquiv t).symm leaf) j w.1).2,w.2) i⟫_ℝ|

theorem hitBy_covered {K : ℝ} (hK : 0<K) (N fuel : ℕ) (s₀ : State (t+1) (4096*J^2+1) ell)
    (hs : Ready s₀) (hell : 0<ell) (w : Raw d n r J E H t × Seed)
    (hhit : hitBy P B fallback t leaf j policy K N fuel s₀ w) :
    arrayHit P B fallback t leaf j policy K N fuel s₀ w := by
  obtain ⟨i,hi,hh⟩ := hhit
  cases hq : MarkPolicyReplay.run P B fallback t leaf j policy K w.1 i
      (ControllerPolicyDriver.initial policy N w.2 s₀) with
  | ready remaining a s => simp only [hq,BlockedHit] at hh
  | finished a s => simp only [hq,BlockedHit] at hh
  | pending remaining a output phase =>
    cases phase with
    | normal p s => simp only [hq,BlockedHit] at hh
    | delivered p before after => simp only [hq,BlockedHit] at hh
    | frozen p s => simp only [hq,BlockedHit] at hh
    | repairing p s =>
      rw [hq] at hh
      obtain ⟨hstop,act,hact,htrigger⟩ := hh
      have he : act=Action.futureMark leaf j := of_decide_eq_true hact
      subst act
      have hg : TaskState.current s=some leaf ∧ ¬GeometricDisclosure.MarkSupplied s leaf j ∧
          1/3072< |markReadout (assemble P B fallback t w.1) leaf j p.point| :=
        of_decide_eq_true htrigger
      have hv : Visible (TaskState.retired s) (leafNode leaf) :=
        ⟨leaf,hg.1,by intro k; rfl⟩
      have ht : trajectory P B fallback t leaf j policy K N s₀ i
          ((RawMarkFactor.factor t ((leafEquiv t).symm leaf) j w.1).2,w.2)=
            .pending remaining a output (.repairing p s) := by
        exact (MarkPolicyReplay.run_factors P B fallback t leaf j w.1 policy hK i
          (ControllerPolicyDriver.initial policy N w.2 s₀)).symm.trans hq
      obtain ⟨q,hquery⟩ := repairing_covered P B fallback t leaf j policy K N fuel s₀ hs hell
        ((RawMarkFactor.factor t ((leafEquiv t).symm leaf) j w.1).2,w.2)
        i hi remaining a output p s ht hv
      refine ⟨q,?_⟩
      rw [hquery]
      have ha := RawLeafFactor.leaf_a_mark_factor P B fallback t w.1 ((leafEquiv t).symm leaf) j
      rw [← ha]
      exact hg.2.2

theorem actual_hit_implies_hitBy (K : ℝ) (N fuel : ℕ) (s₀ : State (t+1) (4096*J^2+1) ell)
    (w : Raw d n r J E H t × Seed) (i : ℕ) (hi : i≤fuel)
    (hhit : BlockedHit (rules K (assemble P B fallback t w.1)) (blockMark leaf j) (markSupplied leaf j)
      (ControllerPolicyDriver.run policy (rules K (assemble P B fallback t w.1)) (markSupplied leaf j)
        (MarkPolicyReplay.ordinary P B fallback t K w.1) (MarkPolicyReplay.rich P B fallback t K w.1) i
        (ControllerPolicyDriver.initial policy N w.2 s₀))) :
    hitBy P B fallback t leaf j policy K N fuel s₀ w := by
  obtain ⟨k,hk,hh⟩ := actual_hit_has_shadow_hit policy (rules K (assemble P B fallback t w.1))
    (blockMark leaf j) (markSupplied leaf j) (MarkPolicyReplay.ordinary P B fallback t K w.1)
    (MarkPolicyReplay.rich P B fallback t K w.1) (ControllerPolicyDriver.initial policy N w.2 s₀) i hhit
  exact ⟨k,hk.trans hi,hh⟩

end GradientHessian.MarkVisibleQueries
