import GradientHessian.NumericalCachedOracle
import GradientHessian.GeometricMemoryReadouts
import GradientHessian.GeometricRepairMeasurability
import GradientHessian.ComparisonControllerReplay

/-! The numerical shadow's actual geometric rules use only the independent
external leaf factor. Every target-leaf future-mark test is suppressed;
the current prior-task hit uses its explicitly synthesized cached readout. -/

noncomputable section
namespace GradientHessian.NumericalShadowRules
open Classical HigherHierarchy HierarchyAddresses RawHierarchy GeometricRepair
  FrontierState TaskState ComparisonController ComparisonControllerReplay NumericalCachedOracle
open scoped InnerProductSpace

variable {d n r J ell : ℕ} {E : Type} {H : ℕ → Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]
  [MeasurableSpace E] [∀ h,MeasurableSpace (H h)]

def blockLeaf {t m : ℕ} (leaf : Leaf (t+1)) : Action t m → Bool
  | .futureMark q _ => decide (q=leaf)
  | _ => false

variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ)
  (fallback : Fin d → ℝ) (t : ℕ) (leaf : Leaf (t+1))

def cachedHit (w : RawLeafFactor.Rest d n r J E H t) (c : Cache d J)
    (s : State (t+1) (4096*J^2+1) ell) (Z : Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) : Bool :=
  if hc : TaskState.current s=some leaf then
    decide (1/3072 < |⟪c.2 ⟨(s.completed leaf).val,current_live s hc⟩,
      BoundedNumericalTest.test (numericalProjection t Z)⟫_ℝ|)
  else hit (assemble P B fallback t (restore t ((leafEquiv t).symm leaf) w)) s Z

def shadowRules (K : ℝ) (w : RawLeafFactor.Rest d n r J E H t) (c : Cache d J) :
    Rules (t+1) (4096*J^2+1) ell (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)
      (Action t (4096*J^2)) where
  priority := priority t (4096*J^2)
  target := target
  trigger := (suppress (rules K (assemble P B fallback t (restore t ((leafEquiv t).symm leaf) w)))
    (blockLeaf leaf)).trigger
  hit := cachedHit P B fallback t leaf w c

theorem other_readout_eq (x y : Raw d n r J E H t)
    (he : (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x).2=
      (RawLeafFactor.factor t ((leafEquiv t).symm leaf) y).2)
    (q : Leaf (t+1)) (hq : q≠leaf) (j : Fin (4096*J^2+1))
    (Z : Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) :
    markReadout (assemble P B fallback t x) q j Z=markReadout (assemble P B fallback t y) q j Z := by
  have hq' : (leafEquiv t).symm q≠(leafEquiv t).symm leaf := fun h => hq ((leafEquiv t).symm.injective h)
  have hd := RawLeafLocality.rest_eq_other_leaf P B fallback t ((leafEquiv t).symm leaf) x y he
    ((leafEquiv t).symm q) hq'
  exact congrArg (fun a : HigherHierarchy.LeafCoefficients (EuclideanSpace ℝ (Fin d)) E (4096*J^2) =>
    ⟪a.a j,BoundedNumericalTest.test (numericalProjection t Z)⟫_ℝ) hd

theorem other_trigger_eq (x y : Raw d n r J E H t)
    (he : (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x).2=
      (RawLeafFactor.factor t ((leafEquiv t).symm leaf) y).2)
    (K : ℝ) (s : State (t+1) (4096*J^2+1) ell)
    (Z : Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) (a : Action t (4096*J^2))
    (ha : blockLeaf leaf a=false) :
    trigger K (assemble P B fallback t x) s Z a=trigger K (assemble P B fallback t y) s Z a := by
  have hm := RawLeafLocality.rest_eq_memory t ((leafEquiv t).symm leaf) x y he
  cases a with
  | localized h path i => simp only [trigger,localCenter_eq_of_memory P B fallback K t x y hm h path i]
  | old path i j => simp only [trigger,oldReadout_eq_of_memory P B fallback t x y hm path i j Z]
  | inner q k j => simp only [trigger,innerReadout_eq_of_memory P B fallback t x y hm q k j Z]
  | futureMark q k =>
    have hq : q≠leaf := of_decide_eq_false ha
    simp only [trigger,other_readout_eq P B fallback t leaf x y he q hq k Z]

theorem shadow_trigger_exact (K : ℝ) (x : Raw d n r J E H t) (c : Cache d J)
    (s : State (t+1) (4096*J^2+1) ell)
    (Z : Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) (a : Action t (4096*J^2)) :
    (shadowRules P B fallback t leaf K (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x).2 c).trigger s Z a=
      (suppress (rules K (assemble P B fallback t x)) (blockLeaf leaf)).trigger s Z a := by
  cases ha : blockLeaf leaf a with
  | true => simp only [shadowRules,suppress,ha,if_true]
  | false =>
    simp only [shadowRules,suppress,ha,Bool.false_eq_true,if_false]
    apply other_trigger_eq P B fallback t leaf _ x _ K s Z a ha
    have he := congrArg (fun z : RawFirstFactor.Target d n r J × RawLeafFactor.Rest d n r J E H t => z.2)
      ((RawLeafFactor.factor t ((leafEquiv t).symm leaf)).apply_symm_apply ((0,0),
        (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x).2))
    exact he

theorem cached_hit_exact (x : Raw d n r J E H t) (c : Cache d J)
    (s : State (t+1) (4096*J^2+1) ell)
    (hc : ∀ h : TaskState.current s=some leaf,
      c.2 ⟨(s.completed leaf).val,current_live s h⟩=
        (leafCoefficients (assemble P B fallback t x) leaf).a ⟨(s.completed leaf).val,current_live s h⟩)
    (Z : Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) :
    cachedHit P B fallback t leaf (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x).2 c s Z=
      hit (assemble P B fallback t x) s Z := by
  by_cases hs : TaskState.current s=some leaf
  · rw [cachedHit,dif_pos hs,hit_current _ s Z hs]
    rw [hc hs]
    rfl
  · rw [cachedHit,dif_neg hs]
    cases hq : TaskState.current s with
    | none => unfold hit; split <;> simp_all
    | some q =>
      have hne : q≠leaf := fun h => hs (h ▸ hq)
      rw [hit_current _ s Z hq,hit_current _ s Z hq]
      congr 3
      apply other_readout_eq P B fallback t leaf _ x _ q hne
      have he := congrArg (fun z : RawFirstFactor.Target d n r J × RawLeafFactor.Rest d n r J E H t => z.2)
        ((RawLeafFactor.factor t ((leafEquiv t).symm leaf)).apply_symm_apply ((0,0),
          (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x).2))
      exact he

variable [BorelSpace E] [FiniteDimensional ℝ E]
  [∀ h,BorelSpace (H h)] [∀ h,FiniteDimensional ℝ (H h)]
  [MeasurableSpace (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)]
  [BorelSpace (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)]

theorem cached_hit_measurable (s : State (t+1) (4096*J^2+1) ell) :
    Measurable (fun q : (RawLeafFactor.Rest d n r J E H t × Cache d J) ×
      Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t =>
      cachedHit P B fallback t leaf q.1.1 q.1.2 s q.2) := by
  by_cases hc : TaskState.current s=some leaf
  · simp only [cachedHit,dif_pos hc]
    apply measurable_decide_pred
    apply measurableSet_lt measurable_const
    apply Measurable.abs
    apply Measurable.inner
    · fun_prop
    · exact (BoundedNumericalTest.test_contDiff.continuous.measurable).comp
        ((numericalProjection (Y := EuclideanSpace ℝ (Fin d)) (E := E) (H := H)
          (m := 4096*J^2) t).continuous.measurable.comp measurable_snd)
  · have hmap : Measurable (fun q : (RawLeafFactor.Rest d n r J E H t × Cache d J) ×
        Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t =>
        (restore t ((leafEquiv t).symm leaf) q.1.1,q.2)) :=
      ((restore_measurable t ((leafEquiv t).symm leaf)).comp
        (measurable_fst.comp measurable_fst)).prodMk measurable_snd
    have h := (hit_fixed_joint_measurable P B fallback t s).comp hmap
    simpa only [Function.comp_def,cachedHit,dif_neg hc] using h

theorem shadow_trigger_measurable (K : ℝ) (s : State (t+1) (4096*J^2+1) ell)
    (a : Action t (4096*J^2)) :
    Measurable (fun q : (RawLeafFactor.Rest d n r J E H t × Cache d J) ×
      Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t =>
      (shadowRules P B fallback t leaf K q.1.1 q.1.2).trigger s q.2 a) := by
  cases ha : blockLeaf leaf a with
  | true => simp only [shadowRules,suppress,ha,if_true]; exact measurable_const
  | false =>
    have hmap : Measurable (fun q : (RawLeafFactor.Rest d n r J E H t × Cache d J) ×
        Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t =>
        (restore t ((leafEquiv t).symm leaf) q.1.1,q.2)) :=
      ((restore_measurable t ((leafEquiv t).symm leaf)).comp
        (measurable_fst.comp measurable_fst)).prodMk measurable_snd
    have h := (trigger_fixed_joint_measurable P B fallback t K s a).comp hmap
    simpa only [Function.comp_def,shadowRules,suppress,ha,Bool.false_eq_true,if_false,rules] using h

end GradientHessian.NumericalShadowRules
