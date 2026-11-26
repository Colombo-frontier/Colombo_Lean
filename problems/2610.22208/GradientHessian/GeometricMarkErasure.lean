import GradientHessian.GeometricMemoryReadouts
import GradientHessian.RawMarkLocality
import GradientHessian.ComparisonControllerReplay

/-! Replacing one future mark preserves every off-target geometric trigger
and the normal numerical hit before supply. The actual suppressed guarded
execution factors through the original RawMarkFactor external coordinate. -/

noncomputable section
namespace GradientHessian.GeometricRepair
open Classical HigherHierarchy HierarchyAddresses RawHierarchy RawLeafLocality
  FrontierState TaskState GeometricDisclosure ComparisonController ComparisonControllerReplay

variable {d n r J ell : ℕ} {E : Type} {H : ℕ → Type}
variable [MeasurableSpace E] [∀ h, MeasurableSpace (H h)]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h, NormedAddCommGroup (H h)] [∀ h, InnerProductSpace ℝ (H h)]
variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ)
  (t : ℕ) (leaf : Leaf (t+1)) (task : Fin (4096*J^2+1))
  (x y : Raw d n r J E H t)
  (he : (RawMarkFactor.factor t ((leafEquiv t).symm leaf) task x).2=
    (RawMarkFactor.factor t ((leafEquiv t).symm leaf) task y).2)

include he in
theorem other_mark_a_eq (q : Leaf (t+1)) (k : Fin (4096*J^2+1)) (hne : q≠leaf ∨ k≠task) :
    (leafCoefficients (assemble P B fallback t x) q).a k=
      (leafCoefficients (assemble P B fallback t y) q).a k := by
  by_cases hq : q=leaf
  · subst q
    exact RawMarkLocality.rest_eq_other_a P B fallback t _ task x y he k (hne.resolve_left (not_not.mpr rfl))
  · have hi : (leafEquiv t).symm q≠(leafEquiv t).symm leaf :=
      fun h => hq ((leafEquiv t).symm.injective h)
    exact congrArg (fun d => d.a k) (RawMarkLocality.rest_eq_other_leaf P B fallback t _ task x y he _ hi)

include he in
theorem other_markReadout_eq (q : Leaf (t+1)) (k : Fin (4096*J^2+1)) (hne : q≠leaf ∨ k≠task)
    (Z : Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) :
    markReadout (assemble P B fallback t x) q k Z=markReadout (assemble P B fallback t y) q k Z := by
  rw [markReadout,markReadout,other_mark_a_eq P B fallback t leaf task x y he q k hne]

include he in
theorem mark_other_trigger_eq (K : ℝ) (s : State (t+1) (4096*J^2+1) ell)
    (Z : Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)
    (a : Action t (4096*J^2)) (ha : a≠.futureMark leaf task) :
    trigger K (assemble P B fallback t x) s Z a=trigger K (assemble P B fallback t y) s Z a := by
  have hm := RawMarkLocality.rest_eq_memory t ((leafEquiv t).symm leaf) task x y he
  cases a with
  | localized h w i =>
    simp only [trigger,localCenter_eq_of_memory P B fallback K t x y hm h w i]
  | old w i j =>
    simp only [trigger,oldReadout_eq_of_memory P B fallback t x y hm w i j Z]
  | inner q k j =>
    simp only [trigger,innerReadout_eq_of_memory P B fallback t x y hm q k j Z]
  | futureMark q k =>
    have hne : q≠leaf ∨ k≠task := by
      by_cases hq : q=leaf
      · exact Or.inr (fun hk => ha (by rw [hq,hk]))
      · exact Or.inl hq
    simp only [trigger,other_markReadout_eq P B fallback t leaf task x y he q k hne Z]

include he in
theorem mark_normal_hit_eq (s : State (t+1) (4096*J^2+1) ell)
    (hstop : ComparisonControllerReplay.markSupplied leaf task s=false)
    (Z : Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) :
    hit (assemble P B fallback t x) s Z=hit (assemble P B fallback t y) s Z := by
  cases hc : TaskState.current s with
  | none => unfold hit; split <;> simp_all
  | some q =>
    let k : Fin (4096*J^2+1) := ⟨(s.completed q).val,current_live s hc⟩
    have hne : q≠leaf ∨ k≠task := by
      by_cases hq : q=leaf
      · right
        intro hk
        have hn := of_decide_eq_false hstop
        apply hn
        right
        refine ⟨hq ▸ hc,?_⟩
        have hv := congrArg Fin.val hk
        change (s.completed q).val=task.val at hv
        simpa only [hq] using hv.symm.le
      · exact Or.inl hq
    rw [hit_current _ s Z hc,hit_current _ s Z hc]
    rw [other_markReadout_eq P B fallback t leaf task x y he q k hne Z]

def blockMark {t m : ℕ} (leaf : Leaf (t+1)) (task : Fin (m+1)) (a : Action t m) : Bool :=
  decide (a=.futureMark leaf task)

include he in
theorem mark_guarded_replay_eq (K : ℝ) (fuel : ℕ)
    (q : Phase (t+1) (4096*J^2+1) ell
      (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) (Action t (4096*J^2))) :
    guardedRun (suppress (rules K (assemble P B fallback t x)) (blockMark leaf task))
      (ComparisonControllerReplay.markSupplied leaf task) fuel q =
    guardedRun (suppress (rules K (assemble P B fallback t y)) (blockMark leaf task))
      (ComparisonControllerReplay.markSupplied leaf task) fuel q := by
  apply suppressed_guardedRun_congr (rules K (assemble P B fallback t x))
    (rules K (assemble P B fallback t y)) (blockMark leaf task)
    (ComparisonControllerReplay.markSupplied leaf task) rfl rfl
  · intro s _ Z a ha
    exact mark_other_trigger_eq P B fallback t leaf task x y he K s Z a (of_decide_eq_false ha)
  · intro s hs Z
    exact mark_normal_hit_eq P B fallback t leaf task x y he s hs Z

def markShadow (K : ℝ) (fuel : ℕ)
    (q : Phase (t+1) (4096*J^2+1) ell
      (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) (Action t (4096*J^2)))
    (rest : RawMarkFactor.Rest d n r J E H t) :=
  guardedRun (suppress (rules K (assemble P B fallback t
    ((RawMarkFactor.factor t ((leafEquiv t).symm leaf) task).symm (0,rest)))) (blockMark leaf task))
      (ComparisonControllerReplay.markSupplied leaf task) fuel q

theorem mark_guarded_replay_factors (K : ℝ) (fuel : ℕ)
    (q : Phase (t+1) (4096*J^2+1) ell
      (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) (Action t (4096*J^2))) :
    guardedRun (suppress (rules K (assemble P B fallback t x)) (blockMark leaf task))
      (ComparisonControllerReplay.markSupplied leaf task) fuel q =
      markShadow P B fallback t leaf task K fuel q (RawMarkFactor.factor t ((leafEquiv t).symm leaf) task x).2 := by
  apply mark_guarded_replay_eq P B fallback t leaf task x _ _ K fuel q
  simp only [MeasurableEquiv.apply_symm_apply]

end GradientHessian.GeometricRepair
