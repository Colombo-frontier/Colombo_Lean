import GradientHessian.RawMemoryLocality
import GradientHessian.RawMemoryHierarchyFactor
import GradientHessian.RawSubtreeLocality
import GradientHessian.RawLeafLocality

/-! Global memory-factor locality at arbitrary height-one addresses.
The path-local change certificate preserves every off-path subtree and all
ancestor centers; its endpoint permits exactly one memory coordinate. -/

noncomputable section
namespace GradientHessian.RawMemoryGlobalLocality
open RawHierarchy RawSubtreeFactor RawMemoryLocality HigherHierarchy

variable {d n r J : ℕ} {E : Type} {H : ℕ → Type}
variable [MeasurableSpace E] [∀ t, MeasurableSpace (H t)]

theorem old_parts (depth : ℕ) (w : Word depth) (i : Fin 8)
    (j : Fin (FirstHeight.depth (4096*J^2+1)+2)) (x y : Raw d n r J E H (0+depth))
    (he : (RawMemoryHierarchyFactor.oldFactor depth w i j x).2=
      (RawMemoryHierarchyFactor.oldFactor depth w i j y).2) :
    (factor 0 depth w x).2=(factor 0 depth w y).2 ∧
      (RawMemoryFactor.oldFactor i j (selectedRaw 0 depth w x)).2=
      (RawMemoryFactor.oldFactor i j (selectedRaw 0 depth w y)).2 := by
  refine ⟨congrArg (fun z : RawMemoryHierarchyFactor.OldRest d n r J E H depth => z.2) he,?_⟩
  have ht := congrArg Prod.fst he
  change (RawMemoryFactor.oldFactor i j (factor 0 depth w x).1).2=
    (RawMemoryFactor.oldFactor i j (factor 0 depth w y).1).2 at ht
  simpa only [factor_target] using ht

theorem inner_parts (depth : ℕ) (w : Word depth) (i : Fin 8)
    (j : Fin (4096*J^2+1)) (k : Fin (Inner.absoluteDepth+2)) (x y : Raw d n r J E H (0+depth))
    (he : (RawMemoryHierarchyFactor.innerFactor depth w i j k x).2=
      (RawMemoryHierarchyFactor.innerFactor depth w i j k y).2) :
    (factor 0 depth w x).2=(factor 0 depth w y).2 ∧
      (RawMemoryFactor.innerFactor i j k (selectedRaw 0 depth w x)).2=
      (RawMemoryFactor.innerFactor i j k (selectedRaw 0 depth w y)).2 := by
  refine ⟨congrArg (fun z : RawMemoryHierarchyFactor.InnerRest d n r J E H depth => z.2) he,?_⟩
  have ht := congrArg Prod.fst he
  change (RawMemoryFactor.innerFactor i j k (factor 0 depth w x).1).2=
    (RawMemoryFactor.innerFactor i j k (factor 0 depth w y).1).2 at ht
  simpa only [factor_target] using ht

theorem old_pathChange (depth : ℕ) (w : Word depth) (i : Fin 8)
    (j : Fin (FirstHeight.depth (4096*J^2+1)+2)) (x y : Raw d n r J E H (0+depth))
    (he : (RawMemoryHierarchyFactor.oldFactor depth w i j x).2=
      (RawMemoryHierarchyFactor.oldFactor depth w i j y).2) :
    RawSubtreeLocality.PathChange 0 (OldChange i j) depth w x y :=
  RawSubtreeLocality.pathChange_of_rest_eq 0 (OldChange i j) depth w x y
    (old_parts depth w i j x y he).1 (oldChange_of_rest_eq i j _ _ (old_parts depth w i j x y he).2)

theorem inner_pathChange (depth : ℕ) (w : Word depth) (i : Fin 8)
    (j : Fin (4096*J^2+1)) (k : Fin (Inner.absoluteDepth+2)) (x y : Raw d n r J E H (0+depth))
    (he : (RawMemoryHierarchyFactor.innerFactor depth w i j k x).2=
      (RawMemoryHierarchyFactor.innerFactor depth w i j k y).2) :
    RawSubtreeLocality.PathChange 0 (InnerChange i j k) depth w x y :=
  RawSubtreeLocality.pathChange_of_rest_eq 0 (InnerChange i j k) depth w x y
    (inner_parts depth w i j k x y he).1
    (innerChange_of_rest_eq i j k _ _ (inner_parts depth w i j k x y he).2)

theorem all_numerical_of_header (depth : ℕ) (w : Word depth) (x y : Raw d n r J E H (0+depth))
    (he : (factor 0 depth w x).2=(factor 0 depth w y).2)
    (hh : ((selectedRaw 0 depth w x).1,(selectedRaw 0 depth w x).2.1)=
      ((selectedRaw 0 depth w y).1,(selectedRaw 0 depth w y).2.1)) :
    ∀ q, RawLeafFactor.leafNumerical (0+depth) x q=RawLeafFactor.leafNumerical (0+depth) y q := by
  let rel := fun t (a b : Raw d n r J E H t) =>
    ∀ q, RawLeafFactor.leafNumerical t a q=RawLeafFactor.leafNumerical t b q
  have hs : ∀ t (a b : Raw d n r J E H (t+1)),
      (∀ j,rel t (a.1 j) (b.1 j)) → a.2=b.2 → rel (t+1) a b := by
    intro t a b hc _ q
    exact hc q.1 q.2
  apply RawSubtreeLocality.lift_relation rel (fun _ _ _ => rfl) hs 0 depth w x y he
  intro q
  exact congrArg (fun z : RawMemoryFactor.Header d n r J => (z.1 q,z.2 q)) hh

theorem old_all_numerical (depth : ℕ) (w : Word depth) (i : Fin 8)
    (j : Fin (FirstHeight.depth (4096*J^2+1)+2)) (x y : Raw d n r J E H (0+depth))
    (he : (RawMemoryHierarchyFactor.oldFactor depth w i j x).2=
      (RawMemoryHierarchyFactor.oldFactor depth w i j y).2) :
    ∀ q, RawLeafFactor.leafNumerical (0+depth) x q=RawLeafFactor.leafNumerical (0+depth) y q :=
  all_numerical_of_header depth w x y (old_parts depth w i j x y he).1
    (oldChange_of_rest_eq i j _ _ (old_parts depth w i j x y he).2).1

theorem inner_all_numerical (depth : ℕ) (w : Word depth) (i : Fin 8)
    (j : Fin (4096*J^2+1)) (k : Fin (Inner.absoluteDepth+2)) (x y : Raw d n r J E H (0+depth))
    (he : (RawMemoryHierarchyFactor.innerFactor depth w i j k x).2=
      (RawMemoryHierarchyFactor.innerFactor depth w i j k y).2) :
    ∀ q, RawLeafFactor.leafNumerical (0+depth) x q=RawLeafFactor.leafNumerical (0+depth) y q :=
  all_numerical_of_header depth w x y (inner_parts depth w i j k x y he).1
    (innerChange_of_rest_eq i j k _ _ (inner_parts depth w i j k x y he).2).1

end GradientHessian.RawMemoryGlobalLocality
