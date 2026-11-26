import GradientHessian.AugmentedDisclosureStops
import GradientHessian.DirectionFactorActions
import GradientHessian.GeometricMarkErasure

/-! Full public disclosure is independent of an isolated raw coordinate until
that coordinate is supplied or its completion block is disclosed. All other
retired subtrees remain in the packet; no frontier-prefix assumption is used. -/

noncomputable section
namespace GradientHessian.AugmentedDisclosure
open Classical HigherHierarchy HierarchyAddresses RawHierarchy RawDirection
  FrontierState TaskState GeometricRepair GeometricDisclosure

variable {d n r J ell : ℕ} {E : Type} {H : ℕ → Type}
variable [MeasurableSpace E] [∀ h,MeasurableSpace (H h)]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]
variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ)

theorem direction_hidden_of_actionStop {t m : ℕ} (a : Action t m)
    (s : State (t+1) (m+1) ell) (hs : actionStop a s=false) : ¬directionDisclosed s a := by
  cases a with
  | localized h w i => exact of_decide_eq_false hs
  | old w i j => exact of_decide_eq_false hs
  | inner leaf j k =>
    change ¬j.val<(s.completed leaf).val
    exact of_decide_eq_false hs
  | futureMark leaf j => exact not_false

theorem disclosed_direction_eq (K : ℝ) (t : ℕ) (x y : Raw d n r J E H t)
    (a : Action t (4096*J^2)) (q : Slot J t) (ha : directionSlot a=some q)
    (he : Except t q x y) (s : State (t+1) (4096*J^2+1) ell) (hs : actionStop a s=false) :
    ∀ b,directionDisclosed s b →
      direction K (assemble P B fallback t x) b=direction K (assemble P B fallback t y) b := by
  intro b hb
  have hne : directionSlot b≠some q := by
    intro heq
    have hba := directionSlot_unique b a q heq ha
    subst b
    exact direction_hidden_of_actionStop a s hs hb
  cases b with
  | localized h w i =>
    exact center_eq_of_slot P B fallback K t x y q he h w i (fun h => hne (congrArg some h))
  | old w i j =>
    exact oldDirection_eq_of_slot P B fallback t x y q he w i j (fun h => hne (congrArg some h))
  | inner leaf j k =>
    exact innerDirection_eq_of_slot P B fallback t x y q he leaf j k (fun h => hne (congrArg some h))
  | futureMark leaf j => rfl

theorem direction_view_eq_of_numerical (K : ℝ) (t : ℕ) (x y : Raw d n r J E H t)
    (a : Action t (4096*J^2)) (q : Slot J t) (ha : directionSlot a=some q)
    (he : Except t q x y)
    (hn : ∀ leaf,RawLeafFactor.leafNumerical t x leaf=RawLeafFactor.leafNumerical t y leaf)
    (s : State (t+1) (4096*J^2+1) ell) (hs : actionStop a s=false) :
    view K (assemble P B fallback t x) s=view K (assemble P B fallback t y) s := by
  apply view_congr
  · intro leaf _
    simp only [leafCoefficients,RawLeafFactor.leaf_A_assemble,hn]
  · intro leaf j _
    simp only [leafCoefficients,RawLeafFactor.leaf_b_assemble,hn]
  · intro leaf j _
    simp only [leafCoefficients,RawLeafFactor.leaf_a_assemble,hn]
  · exact disclosed_direction_eq P B fallback K t x y a q ha he s hs

theorem center_view_eq (K : ℝ) (h depth : ℕ) (w : Word depth) (i : Fin 8)
    (x y : Raw d n r J E H (h+1+depth))
    (he : (RawCenterFactor.factor h depth w i x).2=(RawCenterFactor.factor h depth w i y).2)
    (s : State (h+1+depth+1) (4096*J^2+1) ell)
    (hs : DirectionPolicyReplay.centerStop h depth w i s=false) :
    view K (assemble P B fallback (h+1+depth) x) s=view K (assemble P B fallback (h+1+depth) y) s := by
  have hn := RawCenterLocality.rest_eq_all_leafData P B fallback h depth w i x y he
  apply view_congr
  · intro leaf _; exact congrArg (fun z => z.A) (hn _)
  · intro leaf j _; exact congrArg (fun z => z.b j) (hn _)
  · intro leaf j _; exact congrArg (fun z => z.a j) (hn _)
  · apply disclosed_direction_eq P B fallback K (h+1+depth) x y
      (centerFactorAction h depth w i) _ (centerFactorAction_slot h depth w i)
      (center_factor_except h depth w i x y he) s
    simpa only [centerFactorAction_stop] using hs

theorem old_view_eq (K : ℝ) (depth : ℕ) (w : Word depth) (i : Fin 8)
    (j : Fin (FirstHeight.depth (4096*J^2+1)+2)) (x y : Raw d n r J E H (0+depth))
    (he : (RawMemoryHierarchyFactor.oldFactor depth w i j x).2=
      (RawMemoryHierarchyFactor.oldFactor depth w i j y).2)
    (s : State (0+depth+1) (4096*J^2+1) ell) (hs : DirectionPolicyReplay.oldStop depth w i s=false) :
    view K (assemble P B fallback (0+depth) x) s=view K (assemble P B fallback (0+depth) y) s := by
  apply direction_view_eq_of_numerical P B fallback K (0+depth) x y
    (oldFactorAction depth w i j) _ (oldFactorAction_slot depth w i j)
    (old_factor_except depth w i j x y he) (RawMemoryGlobalLocality.old_all_numerical depth w i j x y he) s
  simpa only [oldFactorAction_stop] using hs

theorem inner_view_eq (K : ℝ) (depth : ℕ) (w : Word depth) (i : Fin 8)
    (j : Fin (4096*J^2+1)) (k : Fin (Inner.absoluteDepth+2)) (x y : Raw d n r J E H (0+depth))
    (he : (RawMemoryHierarchyFactor.innerFactor depth w i j k x).2=
      (RawMemoryHierarchyFactor.innerFactor depth w i j k y).2)
    (s : State (0+depth+1) (4096*J^2+1) ell)
    (hs : ComparisonControllerReplay.taskDisclosed (leafEquiv (0+depth) (prependSlot 0 depth w i)) j s=false) :
    view K (assemble P B fallback (0+depth) x) s=view K (assemble P B fallback (0+depth) y) s := by
  apply direction_view_eq_of_numerical P B fallback K (0+depth) x y
    (innerFactorAction depth w i j k) _ (innerFactorAction_slot depth w i j k)
    (inner_factor_except depth w i j k x y he)
    (RawMemoryGlobalLocality.inner_all_numerical depth w i j k x y he) s
  simpa only [innerFactorAction_stop] using hs

theorem direction_eq_of_memory (K : ℝ) (t : ℕ) (x y : Raw d n r J E H t)
    (he : RawLeafLocality.memory t x=RawLeafLocality.memory t y) (a : Action t (4096*J^2)) :
    direction K (assemble P B fallback t x) a=direction K (assemble P B fallback t y) a := by
  cases a with
  | localized h w i => exact localCenter_eq_of_memory P B fallback K t x y he h w i
  | old w i j => exact oldDirection_eq_of_memory P B fallback t x y he w i j
  | inner leaf j k => exact congrArg (fun v => v j k) (leaf_v_eq_of_memory P B fallback t x y he leaf)
  | futureMark leaf j => rfl

theorem mark_view_eq (K : ℝ) (t : ℕ) (leaf : Leaf (t+1)) (j : Fin (4096*J^2+1))
    (x y : Raw d n r J E H t)
    (he : (RawMarkFactor.factor t ((leafEquiv t).symm leaf) j x).2=
      (RawMarkFactor.factor t ((leafEquiv t).symm leaf) j y).2)
    (s : State (t+1) (4096*J^2+1) ell) (hs : markStop leaf j s=false) :
    view K (assemble P B fallback t x) s=view K (assemble P B fallback t y) s := by
  have hhidden : ¬MarkSupplied s leaf j := of_decide_eq_false hs
  apply view_congr
  · intro q _
    by_cases hq : q=leaf
    · subst q; exact RawMarkLocality.rest_eq_target_A P B fallback t _ j x y he
    · exact congrArg (fun z => z.A) (RawMarkLocality.rest_eq_other_leaf P B fallback t _ j x y he _
        (fun h => hq ((leafEquiv t).symm.injective h)))
  · intro q k hk
    by_cases hq : q=leaf
    · subst q
      have hkj : k≠j := by intro h; subst k; exact hhidden hk
      exact RawMarkLocality.rest_eq_other_b P B fallback t _ j x y he k hkj
    · exact congrArg (fun z => z.b k) (RawMarkLocality.rest_eq_other_leaf P B fallback t _ j x y he _
        (fun h => hq ((leafEquiv t).symm.injective h)))
  · intro q k hk
    apply other_mark_a_eq P B fallback t leaf j x y he q k
    by_cases hq : q=leaf
    · right; intro hkj; subst q; subst k; exact hhidden (Or.inl hk)
    · exact Or.inl hq
  · intro a _
    exact direction_eq_of_memory P B fallback K t x y (RawMarkLocality.rest_eq_memory t _ j x y he) a

end GradientHessian.AugmentedDisclosure
