import GradientHessian.GeometricDirectionErasure

/-! A raw direction slot names exactly one repair action. Suppressing the
tests of one isolated direction is therefore the source's single-test
suppression, with no extra hidden predicates removed. -/

noncomputable section
namespace GradientHessian.GeometricRepair
open Classical RawDirection HigherHierarchy HierarchyAddresses

def slotLength {J : ℕ} : (t : ℕ) → Slot J t → ℕ
  | 0,.inl _ => 3
  | 0,.inr _ => 4
  | t+1,.inl q => slotLength t q.2+1
  | _+1,.inr _ => 2

theorem slotLength_cast {J a b : ℕ} (he : a=b) (q : Slot J a) :
    slotLength b (castSlot he q)=slotLength a q := by subst b; rfl

theorem castSlot_injective {J a b : ℕ} (he : a=b) : Function.Injective (castSlot (J := J) he) := by
  subst b
  exact fun _ _ he => he

theorem slotLength_embed {J : ℕ} (h : ℕ) : ∀ depth (w : Word depth) (q : Slot J h),
    slotLength (h+depth) (embed h depth w q)=depth+slotLength h q
  | 0,_,_ => by simp [embed]
  | depth+1,w,q => by
      change slotLength (h+depth) (embed h depth (Fin.tail w) q)+1=(depth+1)+slotLength h q
      rw [slotLength_embed h depth (Fin.tail w) q]
      omega

theorem embed_injective {J : ℕ} (h : ℕ) : ∀ depth (w z : Word depth) (q s : Slot J h),
    embed h depth w q=embed h depth z s → w=z ∧ q=s := by
  intro depth
  induction depth with
  | zero => intro w z q s he; exact ⟨Subsingleton.elim _ _,he⟩
  | succ depth ih =>
    intro w z q s he
    have ha := Prod.mk.inj (Sum.inl.inj he)
    obtain ⟨ht,hq⟩ := ih (Fin.tail w) (Fin.tail z) q s ha.2
    refine ⟨?_,hq⟩
    rw [← Fin.cons_self_tail w,← Fin.cons_self_tail z,ha.1,ht]

theorem centerSlot_length {J t : ℕ} (h : Fin t) (w : Word (t-(h.val+1))) (i : Fin 8) :
    slotLength t (centerSlot (J := J) h w i)=t-(h.val+1)+2 := by
  simp only [centerSlot,slotLength_cast,slotLength_embed,slotLength]

theorem oldSlot_length {J : ℕ} (t : ℕ) (w : Word t) (i : Fin 8)
    (j : Fin (FirstHeight.depth (4096*J^2+1)+2)) : slotLength t (oldSlot t w i j)=t+3 := by
  simp only [oldSlot,slotLength_cast,slotLength_embed,slotLength]

theorem innerSlot_length {J : ℕ} : ∀ (t : ℕ) (q : LeafSlot t) (j : Fin (4096*J^2+1))
    (k : Fin (Inner.absoluteDepth+2)),slotLength t (innerSlot t q j k)=t+4
  | 0,_,_,_ => rfl
  | t+1,q,j,k => by simp only [innerSlot,slotLength,innerSlot_length]

theorem centerSlot_ne_oldSlot {J t : ℕ} (h : Fin t) (w : Word (t-(h.val+1))) (i : Fin 8)
    (z : Word t) (a : Fin 8) (b : Fin (FirstHeight.depth (4096*J^2+1)+2)) :
    centerSlot h w i≠oldSlot t z a b := by
  intro he
  have hh := congrArg (slotLength t) he
  simp only [centerSlot_length,oldSlot_length] at hh
  omega

theorem centerSlot_ne_innerSlot {J t : ℕ} (h : Fin t) (w : Word (t-(h.val+1))) (i : Fin 8)
    (q : LeafSlot t) (a : Fin (4096*J^2+1)) (b : Fin (Inner.absoluteDepth+2)) :
    centerSlot h w i≠innerSlot t q a b := by
  intro he
  have hh := congrArg (slotLength t) he
  simp only [centerSlot_length,innerSlot_length] at hh
  omega

theorem oldSlot_ne_innerSlot {J t : ℕ} (w : Word t) (i : Fin 8)
    (j : Fin (FirstHeight.depth (4096*J^2+1)+2)) (q : LeafSlot t)
    (a : Fin (4096*J^2+1)) (b : Fin (Inner.absoluteDepth+2)) :
    oldSlot t w i j≠innerSlot t q a b := by
  intro he
  have hh := congrArg (slotLength t) he
  simp only [oldSlot_length,innerSlot_length] at hh
  omega

theorem centerAction_injective {J t : ℕ} (h k : Fin t)
    (w : Word (t-(h.val+1))) (z : Word (t-(k.val+1))) (i j : Fin 8)
    (he : centerSlot (J := J) h w i=centerSlot k z j) :
    (Action.localized h w i : Action t (4096*J^2))=.localized k z j := by
  have hh := congrArg (slotLength t) he
  simp only [centerSlot_length] at hh
  have hk : h=k := Fin.ext (by have := h.isLt; have := k.isLt; omega)
  subst k
  obtain ⟨hw,hi⟩ := embed_injective (h.val+1) _ w z (.inr i) (.inr j) (castSlot_injective _ he)
  have hij : i=j := Sum.inr.inj hi
  subst z
  subst j
  rfl

theorem oldAction_injective {J t : ℕ} (w z : Word t) (i a : Fin 8)
    (j b : Fin (FirstHeight.depth (4096*J^2+1)+2)) (he : oldSlot t w i j=oldSlot t z a b) :
    (Action.old w i j : Action t (4096*J^2))=.old z a b := by
  obtain ⟨hw,hi⟩ := embed_injective 0 t w z (.inl (i,j)) (.inl (a,b)) (castSlot_injective _ he)
  have hab := Prod.mk.inj (Sum.inl.inj hi)
  rcases hab with ⟨rfl,rfl⟩
  subst z
  rfl

theorem innerSlot_injective {J : ℕ} : ∀ (t : ℕ) (p q : LeafSlot t) (i j : Fin (4096*J^2+1))
    (a b : Fin (Inner.absoluteDepth+2)),innerSlot t p i a=innerSlot t q j b → p=q ∧ i=j ∧ a=b := by
  intro t
  induction t with
  | zero =>
    intro p q i j a b he
    have hh := Prod.mk.inj (Sum.inr.inj he)
    exact ⟨hh.1,(Prod.mk.inj hh.2).1,(Prod.mk.inj hh.2).2⟩
  | succ t ih =>
    intro p q i j a b he
    have hh := Prod.mk.inj (Sum.inl.inj he)
    obtain ⟨ht,hi,ha⟩ := ih p.2 q.2 i j a b hh.2
    exact ⟨Prod.ext hh.1 ht,hi,ha⟩

theorem innerAction_injective {J t : ℕ} (p q : FrontierState.Leaf (t+1))
    (i j : Fin (4096*J^2+1)) (a b : Fin (Inner.absoluteDepth+2))
    (he : innerSlot t ((leafEquiv t).symm p) i a=innerSlot t ((leafEquiv t).symm q) j b) :
    (Action.inner p i a : Action t (4096*J^2))=.inner q j b := by
  obtain ⟨hp,hi,ha⟩ := innerSlot_injective t _ _ i j a b he
  have hpq : p=q := (leafEquiv t).symm.injective hp
  subst q
  subst j
  subst b
  rfl

theorem directionSlot_unique {J t : ℕ} (a b : Action t (4096*J^2)) (q : Slot J t)
    (ha : directionSlot a=some q) (hb : directionSlot b=some q) : a=b := by
  have he := ha.trans hb.symm
  cases a with
  | localized h w i =>
    cases b with
    | localized k z j => exact centerAction_injective h k w z i j (Option.some.inj he)
    | old z j k => exact False.elim (centerSlot_ne_oldSlot h w i z j k (Option.some.inj he))
    | inner p j k => exact False.elim (centerSlot_ne_innerSlot h w i _ j k (Option.some.inj he))
    | futureMark p j => simp only [directionSlot,Option.some_ne_none] at he
  | old w i j =>
    cases b with
    | localized h z k => exact False.elim (centerSlot_ne_oldSlot h z k w i j (Option.some.inj he.symm))
    | old z a b => exact oldAction_injective w z i a j b (Option.some.inj he)
    | inner p a b => exact False.elim (oldSlot_ne_innerSlot w i j _ a b (Option.some.inj he))
    | futureMark p a => simp only [directionSlot,Option.some_ne_none] at he
  | inner p i j =>
    cases b with
    | localized h w k => exact False.elim (centerSlot_ne_innerSlot h w k _ i j (Option.some.inj he.symm))
    | old w a b => exact False.elim (oldSlot_ne_innerSlot w a b _ i j (Option.some.inj he.symm))
    | inner q a b => exact innerAction_injective p q i a j b (Option.some.inj he)
    | futureMark q a => simp only [directionSlot,Option.some_ne_none] at he
  | futureMark p i => exact Option.noConfusion ha

theorem blockDirection_eq_single {J t : ℕ} (a : Action t (4096*J^2)) (q : Slot J t)
    (ha : directionSlot a=some q) : blockDirection q=(fun b => decide (b=a)) := by
  funext b
  by_cases hb : b=a
  · subst b
    simp only [blockDirection,ha,decide_true]
  · have hn : directionSlot b≠some q := fun he => hb (directionSlot_unique b a q he ha)
    simp only [blockDirection,decide_eq_false hn,decide_eq_false hb]

end GradientHessian.GeometricRepair
