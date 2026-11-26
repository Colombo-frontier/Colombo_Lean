import GradientHessian.RawCenterLocality
import GradientHessian.RawMemoryGlobalLocality
import GradientHessian.HierarchyAddressLaws

/-! Typed addresses for every actual direction in the presampled tree.
Changing one isolated factor preserves every other direction exactly. -/

noncomputable section
namespace GradientHessian.RawDirection
open Classical RawHierarchy RawSubtreeFactor RawSubtreeLocality HigherHierarchy

def Slot (J : ℕ) : ℕ → Type
  | 0 => (Fin 8 × Fin (FirstHeight.depth (4096*J^2+1)+2)) ⊕
      (Fin 8 × Fin (4096*J^2+1) × Fin (Inner.absoluteDepth+2))
  | t+1 => (Fin 8 × Slot J t) ⊕ Fin 8

def Value {J : ℕ} (E : Type) (H : ℕ → Type) : (t : ℕ) → Slot J t → Type
  | 0,_ => E
  | t+1,.inl q => Value E H t q.2
  | t+1,.inr _ => H t

def lookup {d n r J : ℕ} {E : Type} {H : ℕ → Type} :
    (t : ℕ) → Raw d n r J E H t → (q : Slot J t) → Value E H t q
  | 0,x,.inl q => x.2.2.2 q.1 q.2
  | 0,x,.inr q => x.2.2.1 q.1 q.2.1 q.2.2
  | t+1,x,.inl q => lookup t (x.1 q.1) q.2
  | t+1,x,.inr q => x.2 q

def embed {J : ℕ} (h : ℕ) : (depth : ℕ) → Word depth → Slot J h → Slot J (h+depth)
  | 0,_,q => q
  | depth+1,w,q => .inl (w 0,embed h depth (Fin.tail w) q)

def castSlot {J a b : ℕ} (he : a=b) : Slot J a → Slot J b := _root_.cast (congrArg (Slot J) he)

variable {d n r J : ℕ} {E : Type} {H : ℕ → Type}

theorem lookup_embed (h : ℕ) : ∀ depth (w : Word depth) (q : Slot J h) (x : Raw d n r J E H (h+depth)),
    HEq (lookup (h+depth) x (embed h depth w q)) (lookup h (selectedRaw h depth w x) q)
  | 0,_,_,_ => HEq.rfl
  | depth+1,w,q,x => lookup_embed h depth (Fin.tail w) q (x.1 (w 0))

theorem lookup_cast {a b : ℕ} (he : a=b) (q : Slot J a) (x : Raw d n r J E H a) :
    HEq (lookup b (HierarchyAddresses.castRaw he x) (castSlot he q)) (lookup a x q) := by
  subst b
  rfl

def Except (t : ℕ) (target : Slot J t) (x y : Raw d n r J E H t) : Prop :=
  ∀ q,q≠target → lookup t x q=lookup t y q

theorem center_except (h : ℕ) (i : Fin 8) (x y : Raw d n r J E H (h+1))
    (hc : RawCenterLocality.LocalChange h i x y) : Except (h+1) (.inr i) x y := by
  intro q hq
  cases q with
  | inl q => change lookup h (x.1 q.1) q.2=lookup h (y.1 q.1) q.2; rw [hc.1]
  | inr q => exact hc.2 q (fun he => hq (congrArg Sum.inr he))

theorem old_except (i : Fin 8) (j : Fin (FirstHeight.depth (4096*J^2+1)+2))
    (x y : Raw d n r J E H 0) (hc : RawMemoryLocality.OldChange i j x y) :
    Except 0 (.inl (i,j)) x y := by
  intro q hq
  cases q with
  | inl q =>
    apply hc.2.2
    by_cases hi : q.1=i
    · exact Or.inr (fun hj => hq (congrArg Sum.inl (Prod.ext hi hj)))
    · exact Or.inl hi
  | inr q => exact congrArg (fun a => a q.1 q.2.1 q.2.2) hc.2.1

theorem inner_except (i : Fin 8) (j : Fin (4096*J^2+1)) (k : Fin (Inner.absoluteDepth+2))
    (x y : Raw d n r J E H 0) (hc : RawMemoryLocality.InnerChange i j k x y) :
    Except 0 (.inr (i,j,k)) x y := by
  intro q hq
  cases q with
  | inl q => exact congrArg (fun a => a q.1 q.2) hc.2.1
  | inr q =>
    apply hc.2.2
    by_cases hi : q.1=i
    · right
      by_cases hj : q.2.1=j
      · exact Or.inr (fun hk => hq (congrArg Sum.inr (Prod.ext hi (Prod.ext hj hk))))
      · exact Or.inl hj
    · exact Or.inl hi

theorem except_path (h : ℕ) (target : Slot J h)
    (rel : Raw d n r J E H h → Raw d n r J E H h → Prop)
    (hend : ∀ x y,rel x y → Except h target x y) :
    ∀ depth (w : Word depth) (x y : Raw d n r J E H (h+depth)),
    PathChange h rel depth w x y → Except (h+depth) (embed h depth w target) x y := by
  intro depth
  induction depth with
  | zero => intro w x y hc; exact hend x y hc
  | succ depth ih =>
    intro w x y hc q hq
    cases q with
    | inr q => exact congrFun hc.1 q
    | inl q =>
      change lookup (h+depth) (x.1 q.1) q.2=lookup (h+depth) (y.1 q.1) q.2
      by_cases hi : q.1=w 0
      · rw [hi]
        apply ih (Fin.tail w) _ _ hc.2.2 q.2
        intro he
        apply hq
        exact congrArg Sum.inl (Prod.ext hi he)
      · rw [hc.2.1 q.1 hi]

variable [MeasurableSpace E] [∀ t,MeasurableSpace (H t)]

theorem center_factor_except (h depth : ℕ) (w : Word depth) (i : Fin 8)
    (x y : Raw d n r J E H (h+1+depth))
    (he : (RawCenterFactor.factor h depth w i x).2=(RawCenterFactor.factor h depth w i y).2) :
    Except (h+1+depth) (embed (h+1) depth w (.inr i)) x y :=
  except_path (h+1) (.inr i) (RawCenterLocality.LocalChange h i) (center_except h i)
    depth w x y (RawCenterLocality.pathChange_of_rest_eq h depth w i x y he)

theorem old_factor_except (depth : ℕ) (w : Word depth) (i : Fin 8)
    (j : Fin (FirstHeight.depth (4096*J^2+1)+2)) (x y : Raw d n r J E H (0+depth))
    (he : (RawMemoryHierarchyFactor.oldFactor depth w i j x).2=(RawMemoryHierarchyFactor.oldFactor depth w i j y).2) :
    Except (0+depth) (embed 0 depth w (.inl (i,j))) x y :=
  except_path 0 (.inl (i,j)) (RawMemoryLocality.OldChange i j) (old_except i j)
    depth w x y (RawMemoryGlobalLocality.old_pathChange depth w i j x y he)

theorem inner_factor_except (depth : ℕ) (w : Word depth) (i : Fin 8)
    (j : Fin (4096*J^2+1)) (k : Fin (Inner.absoluteDepth+2)) (x y : Raw d n r J E H (0+depth))
    (he : (RawMemoryHierarchyFactor.innerFactor depth w i j k x).2=
      (RawMemoryHierarchyFactor.innerFactor depth w i j k y).2) :
    Except (0+depth) (embed 0 depth w (.inr (i,j,k))) x y :=
  except_path 0 (.inr (i,j,k)) (RawMemoryLocality.InnerChange i j k) (inner_except i j k)
    depth w x y (RawMemoryGlobalLocality.inner_pathChange depth w i j k x y he)

end GradientHessian.RawDirection
