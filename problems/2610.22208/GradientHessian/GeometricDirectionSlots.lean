import GradientHessian.RawDirectionSlots
import GradientHessian.GeometricRepairRules
import GradientHessian.RawFactorCoefficients

/-! Every direction-dependent repair test reads its literal typed raw slot.
Physical coordinates remain the shared height/register projections. -/

noncomputable section
namespace GradientHessian.GeometricRepair
open Classical RawDirection RawHierarchy HierarchyAddresses HigherHierarchy

def centerSlot {J t : ℕ} (h : Fin t) (w : Word (t-(h.val+1))) (i : Fin 8) : Slot J t :=
  castSlot (Nat.add_sub_of_le (Nat.succ_le_of_lt h.isLt)) (embed (h.val+1) (t-(h.val+1)) w (.inr i))

def oldSlot {J : ℕ} (t : ℕ) (w : Word t) (i : Fin 8)
    (j : Fin (FirstHeight.depth (4096*J^2+1)+2)) : Slot J t :=
  castSlot (Nat.zero_add t) (embed 0 t w (.inl (i,j)))

def innerSlot {J : ℕ} : (t : ℕ) → LeafSlot t → Fin (4096*J^2+1) → Fin (Inner.absoluteDepth+2) → Slot J t
  | 0,i,j,k => .inr (i,j,k)
  | t+1,i,j,k => .inl (i.1,innerSlot t i.2 j k)

def directionSlot {J t : ℕ} : Action t (4096*J^2) → Option (Slot J t)
  | .localized h w i => some (centerSlot h w i)
  | .old w i j => some (oldSlot t w i j)
  | .inner leaf j k => some (innerSlot t ((leafEquiv t).symm leaf) j k)
  | .futureMark _ _ => none

variable {d n r J : ℕ} {E : Type} {H : ℕ → Type}

theorem lookup_recast {a b : ℕ} (he : a=b) (q : Slot J a) (x : Raw d n r J E H b) :
    HEq (lookup b x (castSlot he q)) (lookup a (castRaw he.symm x) q) := by subst b; rfl

theorem centerSlot_lookup (t : ℕ) (h : Fin t) (w : Word (t-(h.val+1))) (i : Fin 8)
    (x : Raw d n r J E H t) :
    HEq (lookup t x (centerSlot h w i))
      ((rawAtHeight t (h.val+1) (Nat.succ_le_of_lt h.isLt) w x).2 i) := by
  apply (lookup_recast (Nat.add_sub_of_le (Nat.succ_le_of_lt h.isLt)) _ x).trans
  apply (lookup_embed (h.val+1) (t-(h.val+1)) w (.inr i) _).trans
  rw [← rawAt_eq_selectedRaw]
  rfl

theorem oldSlot_lookup (t : ℕ) (w : Word t) (i : Fin 8)
    (j : Fin (FirstHeight.depth (4096*J^2+1)+2)) (x : Raw d n r J E H t) :
    HEq (lookup t x (oldSlot t w i j)) ((rawAtHeight t 0 (Nat.zero_le t) w x).2.2.2 i j) := by
  apply (lookup_recast (Nat.zero_add t) _ x).trans
  apply (lookup_embed 0 t w (.inl (i,j)) _).trans
  rw [← rawAt_eq_selectedRaw]
  rfl

theorem innerSlot_lookup : ∀ (t : ℕ) (q : LeafSlot t) (j : Fin (4096*J^2+1))
    (k : Fin (Inner.absoluteDepth+2)) (x : Raw d n r J E H t),
    HEq (lookup t x (innerSlot t q j k)) (RawLeafLocality.leafMemory t (RawLeafLocality.memory t x) q j k)
  | 0,_,_,_,_ => HEq.rfl
  | t+1,q,j,k,x => innerSlot_lookup t q.2 j k (x.1 q.1)

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]
variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ)

theorem center_eq_of_slot (K : ℝ) (t : ℕ) (x y : Raw d n r J E H t) (target : Slot J t)
    (he : Except t target x y) (h : Fin t) (w : Word (t-(h.val+1))) (i : Fin 8)
    (hne : centerSlot h w i≠target) :
    localCenter K (assemble P B fallback t x) h w i=localCenter K (assemble P B fallback t y) h w i := by
  have hd := eq_of_heq ((centerSlot_lookup t h w i x).symm.trans
    ((heq_of_eq (he _ hne)).trans (centerSlot_lookup t h w i y)))
  simp only [localCenter,dataAtHeight_assemble]
  exact congrArg (fun v => radius (4096*J^2) K h.val • v) hd

theorem oldDirection_eq_of_slot (t : ℕ) (x y : Raw d n r J E H t) (target : Slot J t)
    (he : Except t target x y) (w : Word t) (i : Fin 8)
    (j : Fin (FirstHeight.depth (4096*J^2+1)+2)) (hne : oldSlot t w i j≠target) :
    oldDirection (assemble P B fallback t x) w i j=oldDirection (assemble P B fallback t y) w i j := by
  have hd := eq_of_heq ((oldSlot_lookup t w i j x).symm.trans
    ((heq_of_eq (he _ hne)).trans (oldSlot_lookup t w i j y)))
  simpa only [oldDirection,oldData,dataAtHeight_assemble] using hd

theorem innerDirection_eq_of_slot (t : ℕ) (x y : Raw d n r J E H t) (target : Slot J t)
    (he : Except t target x y) (leaf : FrontierState.Leaf (t+1))
    (j : Fin (4096*J^2+1)) (k : Fin (Inner.absoluteDepth+2))
    (hne : innerSlot t ((leafEquiv t).symm leaf) j k≠target) :
    (leafCoefficients (assemble P B fallback t x) leaf).v j k=
      (leafCoefficients (assemble P B fallback t y) leaf).v j k := by
  have hd := eq_of_heq ((innerSlot_lookup t ((leafEquiv t).symm leaf) j k x).symm.trans
    ((heq_of_eq (he _ hne)).trans (innerSlot_lookup t ((leafEquiv t).symm leaf) j k y)))
  simpa only [leafCoefficients,RawLeafLocality.leaf_v_assemble] using hd

theorem trigger_eq_of_slot {ell : ℕ} (K : ℝ) (t : ℕ) (x y : Raw d n r J E H t) (target : Slot J t)
    (he : Except t target x y)
    (ha : ∀ q j,(leafData t (assemble P B fallback t x) q).a j=(leafData t (assemble P B fallback t y) q).a j)
    (s : TaskState.State (t+1) (4096*J^2+1) ell)
    (Z : Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)
    (a : Action t (4096*J^2)) (hne : directionSlot a≠some target) :
    trigger K (assemble P B fallback t x) s Z a=trigger K (assemble P B fallback t y) s Z a := by
  cases a with
  | localized h w i =>
    have hi : centerSlot h w i≠target := fun hh => hne (congrArg some hh)
    simp only [trigger,center_eq_of_slot P B fallback K t x y target he h w i hi]
  | old w i j =>
    have hi : oldSlot t w i j≠target := fun hh => hne (congrArg some hh)
    simp only [trigger,oldReadout,oldDirection_eq_of_slot P B fallback t x y target he w i j hi]
  | inner leaf j k =>
    have hi : innerSlot t ((leafEquiv t).symm leaf) j k≠target := fun hh => hne (congrArg some hh)
    simp only [trigger,innerReadout,innerDirection_eq_of_slot P B fallback t x y target he leaf j k hi]
  | futureMark leaf j => simp only [trigger,markReadout,leafCoefficients,ha]

theorem hit_eq_of_leaf_a {ell : ℕ} (t : ℕ) (x y : Raw d n r J E H t)
    (ha : ∀ q j,(leafData t (assemble P B fallback t x) q).a j=(leafData t (assemble P B fallback t y) q).a j)
    (s : TaskState.State (t+1) (4096*J^2+1) ell)
    (Z : Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) :
    hit (assemble P B fallback t x) s Z=hit (assemble P B fallback t y) s Z := by
  cases hc : TaskState.current s with
  | none => unfold hit; split <;> simp_all
  | some leaf =>
    rw [hit_current _ s Z hc,hit_current _ s Z hc]
    simp only [markReadout,leafCoefficients,ha]

end GradientHessian.GeometricRepair
