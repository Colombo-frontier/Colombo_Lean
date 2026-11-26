import GradientHessian.ControllerPolicyDriver
import GradientHessian.CensoredPolicyReplies
import GradientHessian.CensoredMarkOracle

/-! Stateful future-mark erasure. The entire adaptive policy/controller
configuration and each selected point depend only on the external factor
coordinate, up to mark supply, when the target repair predicate is
suppressed. Both replies are the literal full physical censored decoders. -/

noncomputable section
namespace GradientHessian.MarkPolicyReplay
open Classical HigherHierarchy HierarchyAddresses RawHierarchy CensoredHierarchy
open FrontierState TaskState GeometricRepair ComparisonController ComparisonControllerReplay

variable {d n r J ell : ℕ} {E : Type} {H : ℕ → Type}
variable [MeasurableSpace E] [∀ h,MeasurableSpace (H h)]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]
variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ)
  (t : ℕ) (target : Leaf (t+1)) (j : Fin (4096*J^2+1))

def ordinary (K : ℝ) (x : Raw d n r J E H t) :=
  CensoredPolicy.ordinaryReply (ell := ell) K t (coefficients P B fallback t x)

def rich (K : ℝ) (x : Raw d n r J E H t) :=
  CensoredPolicy.richReply (ell := ell) K t (coefficients P B fallback t x)

variable (x y : Raw d n r J E H t)
  (he : (RawMarkFactor.factor t ((leafEquiv t).symm target) j x).2=
    (RawMarkFactor.factor t ((leafEquiv t).symm target) j y).2)

include he in
theorem ordinary_eq {K : ℝ} (hK : 0<K)
    (before after : State (t+1) (4096*J^2+1) ell)
    (hs : markSupplied target j before=false)
    (Z : Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) :
    ordinary P B fallback t K x before after Z=ordinary P B fallback t K y before after Z := by
  unfold ordinary
  cases hc : TaskState.current before with
  | none => rw [CensoredPolicy.ordinaryReply_none _ _ _ _ _ hc,CensoredPolicy.ordinaryReply_none _ _ _ _ _ hc]
  | some cur =>
    rw [CensoredPolicy.ordinaryReply_current _ _ _ _ _ cur hc,CensoredPolicy.ordinaryReply_current _ _ _ _ _ cur hc]
    simp only [decode_coefficients]
    exact CensoredMark.controller_product_reply_eq P B fallback t target j x y he hK before after cur hc hs Z

include he in
theorem rich_eq {K : ℝ} (hK : 0<K)
    (before after : State (t+1) (4096*J^2+1) ell)
    (hs : markSupplied target j before=false)
    (Z : Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) :
    rich P B fallback t K x before after Z=rich P B fallback t K y before after Z := by
  unfold rich
  cases hc : TaskState.current before with
  | none => rw [CensoredPolicy.richReply_none _ _ _ _ _ hc,CensoredPolicy.richReply_none _ _ _ _ _ hc]
  | some cur =>
    rw [CensoredPolicy.richReply_current _ _ _ _ _ cur hc,CensoredPolicy.richReply_current _ _ _ _ _ cur hc]
    exact CensoredMark.controller_rich_eq P B fallback t target j x y he hK before after cur hc hs Z

variable {Seed S : Type*} [MeasurableSpace Seed] [MeasurableSpace S]
variable [MeasurableSpace (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)]
variable [MeasurableSpace (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))]
variable [MeasurableSpace (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ) ×
  (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ]
    Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))]
variable (policy : Machine.Policy Seed S (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)
  (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))
  (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ) ×
    (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ]
      Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ)))

def run (K : ℝ) (raw : Raw d n r J E H t) (fuel : ℕ)
    (q : ControllerPolicyDriver.Config (t+1) (4096*J^2+1) ell S
      (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) (Action t (4096*J^2))) :=
  ControllerPolicyDriver.run policy (suppress (rules K (assemble P B fallback t raw)) (blockMark target j))
    (markSupplied target j) (ordinary P B fallback t K raw) (rich P B fallback t K raw) fuel q

include he in
theorem run_eq {K : ℝ} (hK : 0<K) (fuel : ℕ)
    (q : ControllerPolicyDriver.Config (t+1) (4096*J^2+1) ell S
      (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) (Action t (4096*J^2))) :
    run P B fallback t target j policy K x fuel q=run P B fallback t target j policy K y fuel q := by
  unfold run
  apply ControllerPolicyDriver.run_congr policy
    (suppress (rules K (assemble P B fallback t x)) (blockMark target j))
    (suppress (rules K (assemble P B fallback t y)) (blockMark target j)) (markSupplied target j) rfl rfl
  · intro s _ Z a
    cases hb : blockMark target j a with
    | true => simp [suppress,hb]
    | false =>
      simpa only [suppress,hb,Bool.false_eq_true,if_false] using
        mark_other_trigger_eq P B fallback t target j x y he K s Z a (of_decide_eq_false hb)
  · intro s hs Z
    exact mark_normal_hit_eq P B fallback t target j x y he s hs Z
  · intro before after hs _ Z
    exact ordinary_eq P B fallback t target j x y he hK before after hs Z
  · intro before after hs _ Z
    exact rich_eq P B fallback t target j x y he hK before after hs Z

/-- This executable shadow receives the original factor's external
coordinate and no target mark. Its replacement mark is the fixed zero. -/
def shadow (K : ℝ) (rest : RawMarkFactor.Rest d n r J E H t) (fuel : ℕ)
    (q : ControllerPolicyDriver.Config (t+1) (4096*J^2+1) ell S
      (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) (Action t (4096*J^2))) :=
  run P B fallback t target j policy K
    ((RawMarkFactor.factor t ((leafEquiv t).symm target) j).symm (0,rest)) fuel q

theorem run_factors {K : ℝ} (hK : 0<K) (fuel : ℕ)
    (q : ControllerPolicyDriver.Config (t+1) (4096*J^2+1) ell S
      (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) (Action t (4096*J^2))) :
    run P B fallback t target j policy K x fuel q=
      shadow P B fallback t target j policy K
        (RawMarkFactor.factor t ((leafEquiv t).symm target) j x).2 fuel q := by
  apply run_eq P B fallback t target j x _ _ policy hK fuel q
  simp only [MeasurableEquiv.apply_symm_apply]

theorem selected_factors {K : ℝ} (hK : 0<K) (fuel : ℕ)
    (q : ControllerPolicyDriver.Config (t+1) (4096*J^2+1) ell S
      (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) (Action t (4096*J^2))) :
    ControllerPolicyDriver.selected policy (markSupplied target j) (run P B fallback t target j policy K x fuel q)=
      ControllerPolicyDriver.selected policy (markSupplied target j)
        (shadow P B fallback t target j policy K
          (RawMarkFactor.factor t ((leafEquiv t).symm target) j x).2 fuel q) := by
  rw [run_factors P B fallback t target j x policy hK fuel q]

end GradientHessian.MarkPolicyReplay
