import GradientHessian.AugmentedPolicyReplies
import GradientHessian.GeometricPolicyLedger

/-! The augmented callbacks are the literal true jet and the complete
post-operation public packet on every actual receipt. Controller invariants
are derived for every prefix from the initial state, not assumed of a run. -/

noncomputable section
namespace GradientHessian.AugmentedPolicy
open Classical HigherHierarchy HierarchyAddresses RawHierarchy FrontierState TaskState TaskSlots
  GeometricRepair GeometricDisclosure AugmentedDisclosure ComparisonController JetLocality

variable {d n r J ell : ℕ} {E : Type} {H : ℕ → Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]
variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ)
  (t : ℕ) (x : Raw d n r J E H t)

theorem ordinary_true_receipt {K : ℝ} (hK : 0<K)
    (hd : Valid (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t (assemble P B fallback t x))
    (s : State (t+1) (4096*J^2+1) ell) (p : Pending (DirectionPolicyReplay.Point d J E H t))
    (hs : Ready s) (hc : LastChildClosed (TaskState.retired s)) :
    ordinary P B fallback K t x (serve (rules K (assemble P B fallback t x)) p s).beforeNormal
      (serve (rules K (assemble P B fallback t x)) p s).afterNormal p.point=
      (ordinaryJet (scalar K t (assemble P B fallback t x)) p.point,
        view K (assemble P B fallback t x) (serve (rules K (assemble P B fallback t x)) p s).afterNormal) := by
  apply Prod.ext
  · change DirectionPolicy.ordinary K t (coefficients P B fallback t x) _ _ p.point=_
    rw [DirectionPolicy.ordinary_receipt K t (coefficients P B fallback t x) _ p s hs]
    have h := CensoredPolicy.serve_completedOrdinary hK t (coefficients P B fallback t x) s p hs hc
      (fun leaf => by
        simpa only [decode_coefficients] using
          (leafData_valid t (assemble P B fallback t x) hd ((leafEquiv t).symm leaf)).2.2.1)
    simpa only [decode_coefficients] using h
  · rfl

theorem rich_true_receipt {K : ℝ} (hK : 0<K)
    (s : State (t+1) (4096*J^2+1) ell) (p : Pending (DirectionPolicyReplay.Point d J E H t))
    (hs : Ready s) (hc : LastChildClosed (TaskState.retired s)) :
    rich P B fallback K t x (serve (rules K (assemble P B fallback t x)) p s).beforeNormal
      (serve (rules K (assemble P B fallback t x)) p s).afterNormal p.point=
      (richJet (scalar K t (assemble P B fallback t x)) p.point,
        view K (assemble P B fallback t x) (serve (rules K (assemble P B fallback t x)) p s).afterNormal) := by
  apply Prod.ext
  · change DirectionPolicy.rich K t (coefficients P B fallback t x) _ _ p.point=_
    rw [DirectionPolicy.rich_receipt K t (coefficients P B fallback t x) _ p s hs]
    simpa only [decode_coefficients] using CensoredPolicy.serve_completedRich hK t
      (coefficients P B fallback t x) s p hs hc
  · rfl

theorem prefix_true_replies {K : ℝ} (hK : 0<K)
    (hd : Valid (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t (assemble P B fallback t x)) (hell : 0<ell)
    (ps : List (Pending (DirectionPolicyReplay.Point d J E H t))) (p : Pending (DirectionPolicyReplay.Point d J E H t)) :
    let R := rules (ell := ell) K (assemble P B fallback t x)
    let s := VisibilityWindow.run R ps TaskState.initial
    let c := serve R p s
    ordinary P B fallback K t x c.beforeNormal c.afterNormal p.point=
        (ordinaryJet (scalar K t (assemble P B fallback t x)) p.point,view K (assemble P B fallback t x) c.afterNormal) ∧
      rich P B fallback K t x c.beforeNormal c.afterNormal p.point=
        (richJet (scalar K t (assemble P B fallback t x)) p.point,view K (assemble P B fallback t x) c.afterNormal) := by
  have hs := VisibilityWindow.run_ready (rules K (assemble P B fallback t x)) ps (initial_ready hell) hell
  have hc := GeometricPolicyLedger.run_lastChildClosed (ell := ell) K (assemble P B fallback t x) ps TaskState.initial
    (initial_lastChildClosed (by omega : 0<4096*J^2+1))
  exact ⟨ordinary_true_receipt P B fallback t x hK hd _ p hs hc,rich_true_receipt P B fallback t x hK _ p hs hc⟩

theorem initial_supplied_mark (leaf : Leaf (t+1)) (hc : TaskState.current (TaskState.initial : State (t+1) (4096*J^2+1) ell)=some leaf) :
    mark (assemble P B fallback t x) (TaskState.initial : State (t+1) (4096*J^2+1) ell) leaf ⟨0,by omega⟩=
      (leafCoefficients (assemble P B fallback t x) leaf).b ⟨0,by omega⟩ :=
  mark_supplied _ _ leaf _ (Or.inr ⟨hc,rfl⟩)

end GradientHessian.AugmentedPolicy
