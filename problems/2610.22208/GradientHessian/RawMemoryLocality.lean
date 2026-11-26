import GradientHessian.RawMemoryFactor

/-! Exact field locality of old and inner memory sphere factors. The
complete numerical header is preserved, and only the addressed direction
may change inside its memory family. -/

noncomputable section
namespace GradientHessian.RawMemoryLocality
open RawFirstHeight RawMemoryFactor

variable {d n r J : ℕ} {E : Type} [MeasurableSpace E]

def OldChange (i : Fin 8) (j : Fin (FirstHeight.depth (4096*J^2+1)+2))
    (x y : Raw d n r J E) : Prop :=
  (x.1,x.2.1)=(y.1,y.2.1) ∧ x.2.2.1=y.2.2.1 ∧
    ∀ a b,a≠i ∨ b≠j → x.2.2.2 a b=y.2.2.2 a b

def InnerChange (i : Fin 8) (j : Fin (4096*J^2+1)) (k : Fin (Inner.absoluteDepth+2))
    (x y : Raw d n r J E) : Prop :=
  (x.1,x.2.1)=(y.1,y.2.1) ∧ x.2.2.2=y.2.2.2 ∧
    ∀ a b c,a≠i ∨ b≠j ∨ c≠k → x.2.2.1 a b c=y.2.2.1 a b c

theorem oldChange_of_rest_eq (i : Fin 8) (j : Fin (FirstHeight.depth (4096*J^2+1)+2))
    (x y : Raw d n r J E) (he : (oldFactor i j x).2=(oldFactor i j y).2) :
    OldChange i j x y := by
  refine ⟨congrArg (fun z : OldRest d n r J E => z.1.1) he,
    congrArg (fun z : OldRest d n r J E => z.1.2) he,?_⟩
  intro a b hab
  by_cases ha : a=i
  · subst a
    have hb : b≠j := hab.resolve_left (not_not_intro rfl)
    obtain ⟨q,rfl⟩ := Fin.exists_succAbove_eq hb
    exact congrArg (fun z : OldRest d n r J E => z.2.1 q) he
  · obtain ⟨q,rfl⟩ := Fin.exists_succAbove_eq ha
    exact congrArg (fun z : OldRest d n r J E => z.2.2 q b) he

theorem innerChange_of_rest_eq (i : Fin 8) (j : Fin (4096*J^2+1)) (k : Fin (Inner.absoluteDepth+2))
    (x y : Raw d n r J E) (he : (innerFactor i j k x).2=(innerFactor i j k y).2) :
    InnerChange i j k x y := by
  refine ⟨congrArg (fun z : InnerRest d n r J E => z.1) he,
    congrArg (fun z : InnerRest d n r J E => z.2.2) he,?_⟩
  intro a b c habc
  by_cases ha : a=i
  · subst a
    by_cases hb : b=j
    · subst b
      have hc : c≠k := (habc.resolve_left (not_not_intro rfl)).resolve_left (not_not_intro rfl)
      obtain ⟨q,rfl⟩ := Fin.exists_succAbove_eq hc
      exact congrArg (fun z : InnerRest d n r J E => z.2.1.1.1 q) he
    · obtain ⟨q,rfl⟩ := Fin.exists_succAbove_eq hb
      exact congrArg (fun z : InnerRest d n r J E => z.2.1.1.2 q c) he
  · obtain ⟨q,rfl⟩ := Fin.exists_succAbove_eq ha
    exact congrArg (fun z : InnerRest d n r J E => z.2.1.2 q b c) he

def replaceOld (i : Fin 8) (j : Fin (FirstHeight.depth (4096*J^2+1)+2))
    (z : E) (x : Raw d n r J E) : Raw d n r J E :=
  (oldFactor i j).symm (z,(oldFactor i j x).2)

def replaceInner (i : Fin 8) (j : Fin (4096*J^2+1)) (k : Fin (Inner.absoluteDepth+2))
    (z : E) (x : Raw d n r J E) : Raw d n r J E :=
  (innerFactor i j k).symm (z,(innerFactor i j k x).2)

theorem oldFactor_replace (i : Fin 8) (j : Fin (FirstHeight.depth (4096*J^2+1)+2))
    (z : E) (x : Raw d n r J E) : oldFactor i j (replaceOld i j z x)=(z,(oldFactor i j x).2) :=
  (oldFactor i j).apply_symm_apply _

theorem innerFactor_replace (i : Fin 8) (j : Fin (4096*J^2+1)) (k : Fin (Inner.absoluteDepth+2))
    (z : E) (x : Raw d n r J E) : innerFactor i j k (replaceInner i j k z x)=(z,(innerFactor i j k x).2) :=
  (innerFactor i j k).apply_symm_apply _

theorem replaceOld_direction (i : Fin 8) (j : Fin (FirstHeight.depth (4096*J^2+1)+2))
    (z : E) (x : Raw d n r J E) : (replaceOld i j z x).2.2.2 i j=z := by
  rw [← oldFactor_direction i j,oldFactor_replace]

theorem replaceInner_direction (i : Fin 8) (j : Fin (4096*J^2+1)) (k : Fin (Inner.absoluteDepth+2))
    (z : E) (x : Raw d n r J E) : (replaceInner i j k z x).2.2.1 i j k=z := by
  rw [← innerFactor_direction i j k,innerFactor_replace]

theorem replaceOld_change (i : Fin 8) (j : Fin (FirstHeight.depth (4096*J^2+1)+2))
    (z : E) (x : Raw d n r J E) : OldChange i j (replaceOld i j z x) x :=
  oldChange_of_rest_eq i j _ _ (by simpa only using congrArg Prod.snd (oldFactor_replace i j z x))

theorem replaceInner_change (i : Fin 8) (j : Fin (4096*J^2+1)) (k : Fin (Inner.absoluteDepth+2))
    (z : E) (x : Raw d n r J E) : InnerChange i j k (replaceInner i j k z x) x :=
  innerChange_of_rest_eq i j k _ _ (by simpa only using congrArg Prod.snd (innerFactor_replace i j k z x))

end GradientHessian.RawMemoryLocality
