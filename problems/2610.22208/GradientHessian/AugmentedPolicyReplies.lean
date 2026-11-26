import GradientHessian.AugmentedDisclosureErasure
import GradientHessian.AugmentedDisclosureMeasurability
import GradientHessian.DirectionPolicyMeasurability
import GradientHessian.CensoredMarkOracle
import GradientHessian.DirectionFactorTests

/-! Replies of the stronger comparison policy: the full physical jet and
the complete public disclosure packet after normal processing. The packet
also serves as an input to policy initialization before its first point. -/

noncomputable section
namespace GradientHessian.AugmentedPolicy
open Classical HigherHierarchy HierarchyAddresses RawHierarchy CensoredHierarchy
  FrontierState TaskState GeometricRepair GeometricDisclosure AugmentedDisclosure
  ComparisonController

variable {d n r J ell : ℕ} {E : Type} {H : ℕ → Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]

abbrev Packet (d J : ℕ) (E : Type) (H : ℕ → Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)] (t ell : ℕ) :=
  View (EuclideanSpace ℝ (Fin d)) E H t (4096*J^2) ell

abbrev Ordinary (d J : ℕ) (E : Type) (H : ℕ → Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)] (t ell : ℕ) :=
  DirectionPolicyReplay.Ordinary d J E H t × Packet d J E H t ell

abbrev Rich (d J : ℕ) (E : Type) (H : ℕ → Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)] (t ell : ℕ) :=
  DirectionPolicyReplay.Rich d J E H t × Packet d J E H t ell

variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ)

def ordinary (K : ℝ) (t : ℕ) (x : Raw d n r J E H t)
    (before after : State (t+1) (4096*J^2+1) ell) (Z : DirectionPolicyReplay.Point d J E H t) :
    Ordinary d J E H t ell :=
  (DirectionPolicy.ordinary K t (coefficients P B fallback t x) before after Z,
    view K (assemble P B fallback t x) after)

def rich (K : ℝ) (t : ℕ) (x : Raw d n r J E H t)
    (before after : State (t+1) (4096*J^2+1) ell) (Z : DirectionPolicyReplay.Point d J E H t) :
    Rich d J E H t ell :=
  (DirectionPolicy.rich K t (coefficients P B fallback t x) before after Z,
    view K (assemble P B fallback t x) after)

variable [MeasurableSpace E] [∀ h,MeasurableSpace (H h)]

theorem center_replies_eq {K : ℝ} (hK : 0<K) (h depth : ℕ) (w : Word depth) (i : Fin 8)
    (x y : Raw d n r J E H (h+1+depth))
    (he : (RawCenterFactor.factor h depth w i x).2=(RawCenterFactor.factor h depth w i y).2)
    (before after : State (h+1+depth+1) (4096*J^2+1) ell)
    (hs : DirectionPolicyReplay.centerStop h depth w i after=false)
    (Z : DirectionPolicyReplay.Point d J E H (h+1+depth)) :
    ordinary P B fallback K (h+1+depth) x before after Z=ordinary P B fallback K (h+1+depth) y before after Z ∧
    rich P B fallback K (h+1+depth) x before after Z=rich P B fallback K (h+1+depth) y before after Z := by
  have hr := DirectionPolicy.center_replies_eq P B fallback hK h depth w i x y he before after hs Z
  have hv := center_view_eq P B fallback K h depth w i x y he after hs
  exact ⟨Prod.ext hr.1 hv,Prod.ext hr.2 hv⟩

theorem old_replies_eq {K : ℝ} (hK : 0<K) (depth : ℕ) (w : Word depth) (i : Fin 8)
    (j : Fin (FirstHeight.depth (4096*J^2+1)+2)) (x y : Raw d n r J E H (0+depth))
    (he : (RawMemoryHierarchyFactor.oldFactor depth w i j x).2=
      (RawMemoryHierarchyFactor.oldFactor depth w i j y).2)
    (before after : State (0+depth+1) (4096*J^2+1) ell)
    (hs : DirectionPolicyReplay.oldStop depth w i after=false)
    (Z : DirectionPolicyReplay.Point d J E H (0+depth)) :
    ordinary P B fallback K (0+depth) x before after Z=ordinary P B fallback K (0+depth) y before after Z ∧
    rich P B fallback K (0+depth) x before after Z=rich P B fallback K (0+depth) y before after Z := by
  have hr := DirectionPolicy.old_replies_eq P B fallback hK depth w i j x y he before after hs Z
  have hv := old_view_eq P B fallback K depth w i j x y he after hs
  exact ⟨Prod.ext hr.1 hv,Prod.ext hr.2 hv⟩

theorem inner_replies_eq {K : ℝ} (hK : 0<K) (depth : ℕ) (w : Word depth) (i : Fin 8)
    (j : Fin (4096*J^2+1)) (k : Fin (Inner.absoluteDepth+2)) (x y : Raw d n r J E H (0+depth))
    (he : (RawMemoryHierarchyFactor.innerFactor depth w i j k x).2=
      (RawMemoryHierarchyFactor.innerFactor depth w i j k y).2)
    (before after : State (0+depth+1) (4096*J^2+1) ell)
    (hs : ComparisonControllerReplay.taskDisclosed (leafEquiv (0+depth) (prependSlot 0 depth w i)) j after=false)
    (Z : DirectionPolicyReplay.Point d J E H (0+depth)) :
    ordinary P B fallback K (0+depth) x before after Z=ordinary P B fallback K (0+depth) y before after Z ∧
    rich P B fallback K (0+depth) x before after Z=rich P B fallback K (0+depth) y before after Z := by
  have hr := DirectionPolicy.inner_replies_eq P B fallback hK depth w i j k x y he before after
    (leafEquiv (0+depth) (prependSlot 0 depth w i)) (prependSlot_prefix 0 depth w i) (prepend_last depth w i) hs Z
  have hv := inner_view_eq P B fallback K depth w i j k x y he after hs
  exact ⟨Prod.ext hr.1 hv,Prod.ext hr.2 hv⟩

theorem mark_replies_eq {K : ℝ} (hK : 0<K) (t : ℕ) (leaf : Leaf (t+1)) (j : Fin (4096*J^2+1))
    (x y : Raw d n r J E H t)
    (he : (RawMarkFactor.factor t ((leafEquiv t).symm leaf) j x).2=
      (RawMarkFactor.factor t ((leafEquiv t).symm leaf) j y).2)
    (before after : State (t+1) (4096*J^2+1) ell)
    (hb : markStop leaf j before=false) (ha : markStop leaf j after=false)
    (Z : DirectionPolicyReplay.Point d J E H t) :
    ordinary P B fallback K t x before after Z=ordinary P B fallback K t y before after Z ∧
    rich P B fallback K t x before after Z=rich P B fallback K t y before after Z := by
  have hr : DirectionPolicy.ordinary K t (coefficients P B fallback t x) before after Z=
      DirectionPolicy.ordinary K t (coefficients P B fallback t y) before after Z ∧
      DirectionPolicy.rich K t (coefficients P B fallback t x) before after Z=
      DirectionPolicy.rich K t (coefficients P B fallback t y) before after Z := by
    apply DirectionPolicy.replies_eq hK
    · intro hm
      apply DirectionPolicy.active_of_hidden_task before after hm leaf j
      intro h
      exact (of_decide_eq_false ha) (Or.inl h)
    · intro _ cur hc
      exact CensoredMark.controller_sameKnown P B fallback t leaf j x y he before after cur hc (markStop_open leaf j before hb)
    · intro p
      simpa only [decode_coefficients] using
        CensoredMark.selectedMatrix_eq P B fallback t leaf j x y he p
  have hv := mark_view_eq P B fallback K t leaf j x y he after ha
  exact ⟨Prod.ext hr.1 hv,Prod.ext hr.2 hv⟩

section Measurable
variable [BorelSpace E] [FiniteDimensional ℝ E]
  [∀ h,BorelSpace (H h)] [∀ h,FiniteDimensional ℝ (H h)]
  [∀ t,MeasurableSpace (DirectionPolicyReplay.Point d J E H t)]
  [∀ t,MeasurableSpace (DirectionPolicyReplay.Ordinary d J E H t)]
  [∀ t,MeasurableSpace (DirectionPolicyReplay.Rich d J E H t)]
variable (t : ℕ) [BorelSpace (DirectionPolicyReplay.Point d J E H t)]
  [BorelSpace (DirectionPolicyReplay.Ordinary d J E H t)] [BorelSpace (DirectionPolicyReplay.Rich d J E H t)]

theorem ordinary_fixed_measurable {K : ℝ} (hK : 0<K)
    (before after : State (t+1) (4096*J^2+1) ell) :
    Measurable (fun q : Raw d n r J E H t × DirectionPolicyReplay.Point d J E H t =>
      ordinary P B fallback K t q.1 before after q.2) :=
  (DirectionPolicyReplay.ordinary_fixed_measurable P B fallback t hK before after).prodMk
    ((view_fixed_measurable P B fallback t K after).comp measurable_fst)

theorem rich_fixed_measurable {K : ℝ} (hK : 0<K)
    (before after : State (t+1) (4096*J^2+1) ell) :
    Measurable (fun q : Raw d n r J E H t × DirectionPolicyReplay.Point d J E H t =>
      rich P B fallback K t q.1 before after q.2) :=
  (DirectionPolicyReplay.rich_fixed_measurable P B fallback t hK before after).prodMk
    ((view_fixed_measurable P B fallback t K after).comp measurable_fst)

end Measurable
end GradientHessian.AugmentedPolicy
