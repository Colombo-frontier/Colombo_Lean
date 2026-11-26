import GradientHessian.HigherHierarchyLeafData
import GradientHessian.RawHierarchy
import GradientHessian.FrontierOrder
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Addresses of coefficients and shared physical prefixes

Auxiliary height t is source height t+1. A word chooses coefficient data;
the physical projection depends only on its length, not on that word.
The finite leaf equivalence identifies the source coefficient slots with
the controller's actual lexicographic leaves.
-/

noncomputable section
namespace GradientHessian.HierarchyAddresses

open Classical HigherHierarchy FrontierState

abbrev Word (n : ℕ) := Fin n → Fin 8

def leafWord : (t : ℕ) → LeafSlot t → Word (t+1)
  | 0,i => fun _ => i
  | t+1,i => Fin.cons i.1 (leafWord t i.2)

def wordLeaf : (t : ℕ) → Word (t+1) → LeafSlot t
  | 0,w => w 0
  | t+1,w => (w 0,wordLeaf t (Fin.tail w))

theorem wordLeaf_leafWord : ∀ t (i : LeafSlot t),wordLeaf t (leafWord t i)=i
  | 0,i => rfl
  | t+1,i => by simp [wordLeaf,leafWord,wordLeaf_leafWord t i.2]

theorem leafWord_wordLeaf : ∀ t (w : Word (t+1)),leafWord t (wordLeaf t w)=w
  | 0,w => by funext i; have hi : i=0 := Fin.ext (by have := i.isLt; omega); subst i; rfl
  | t+1,w => by simp only [leafWord,wordLeaf,leafWord_wordLeaf t,Fin.cons_self_tail]

def leafEquiv (t : ℕ) : LeafSlot t ≃ Leaf (t+1) where
  toFun i := toLex (leafWord t i)
  invFun w := wordLeaf t (ofLex w)
  left_inv := wordLeaf_leafWord t
  right_inv := leafWord_wordLeaf t

@[simp] theorem leafEquiv_apply (t : ℕ) (i : LeafSlot t) :
    ofLex (leafEquiv t i)=leafWord t i := rfl

@[simp] theorem leafEquiv_symm_apply (t : ℕ) (w : Leaf (t+1)) :
    (leafEquiv t).symm w=wordLeaf t (ofLex w) := rfl

/-- A coefficient node at depth d. The bottom value d=t is height one. -/
def node (t : ℕ) (d : Fin (t+1)) (w : Word d.val) : Node (t+1) :=
  ⟨⟨d.val,by have := d.isLt; omega⟩,w⟩

@[simp] theorem node_depth (t : ℕ) (d : Fin (t+1)) (w : Word d.val) :
    (node t d w).1.val=d.val := rfl

theorem node_mem_iff (t : ℕ) (d : Fin (t+1)) (w : Word d.val) (leaf : Leaf (t+1)) :
    leaf ∈ subtree (node t d w) ↔ ∀ i : Fin d.val,leaf (i.castLE (by have := d.isLt; omega))=w i :=
  mem_subtree _ _

section Coefficients
universe u
variable {Y E : Type u} {H : ℕ → Type u} {m : ℕ}
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h, NormedAddCommGroup (H h)] [∀ h, InnerProductSpace ℝ (H h)]

def dataAt (h : ℕ) : (depth : ℕ) → Word depth → Data Y E H m (h+depth) → Data Y E H m h
  | 0,_,d => d
  | depth+1,w,d => dataAt h depth (Fin.tail w) (d.children (w 0))

def castData {a b : ℕ} (h : a=b) : Data Y E H m a → Data Y E H m b :=
  _root_.cast (congrArg (Data Y E H m) h)

def dataAtDepth (t : ℕ) (d : Fin (t+1)) (w : Word d.val) (x : Data Y E H m t) :
    Data Y E H m (t-d.val) :=
  dataAt (t-d.val) d.val w (castData (Nat.sub_add_cancel (Nat.le_of_lt_succ d.isLt)).symm x)

def dataAtHeight (t h : ℕ) (hh : h≤t) (w : Word (t-h)) (x : Data Y E H m t) : Data Y E H m h :=
  dataAt h (t-h) w (castData (Nat.add_sub_of_le hh).symm x)

/-- Typed access to a higher node: its physical direction space is H(t-d-1). -/
def localizedData (t : ℕ) (d : Fin t) (w : Word d.val) (x : Data Y E H m t) :
    StepData (Data Y E H m (t-(d.val+1))) (H (t-(d.val+1))) :=
  dataAt (t-(d.val+1)+1) d.val w (castData (by have := d.isLt; omega) x)

def oldData (t : ℕ) (w : Word t) (x : Data Y E H m t) : FirstHeight.Data Y E m :=
  dataAtHeight t 0 (Nat.zero_le t) w x

def dropPrefix (h : ℕ) : (depth : ℕ) → Space Y E H m (h+depth) →L[ℝ] Space Y E H m h
  | 0 => ContinuousLinearMap.id ℝ _
  | depth+1 => (dropPrefix h depth).comp (HigherHierarchy.lower (Space Y E H m (h+depth)) (H (h+depth)))

def castSpace {a b : ℕ} (h : a=b) : Space Y E H m a →L[ℝ] Space Y E H m b := by
  subst b
  exact ContinuousLinearMap.id ℝ _

theorem castSpace_norm_le {a b : ℕ} (h : a=b) : ‖castSpace (Y := Y) (E := E) (H := H) (m := m) h‖ ≤ 1 := by
  subst b
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simp [castSpace]

theorem comp_norm_le_one {A B C : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup C] [NormedSpace ℝ C]
    (f : B →L[ℝ] C) (g : A →L[ℝ] B) (hf : ‖f‖≤1) (hg : ‖g‖≤1) : ‖f.comp g‖≤1 := by
  exact (ContinuousLinearMap.opNorm_comp_le f g).trans
    ((mul_le_mul hf hg (norm_nonneg g) zero_le_one).trans_eq (one_mul 1))

theorem dropPrefix_norm_le (h depth : ℕ) :
    ‖dropPrefix (Y := Y) (E := E) (H := H) (m := m) h depth‖≤1 := by
  induction depth with
  | zero =>
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simp [dropPrefix]
  | succ depth ih => exact comp_norm_le_one _ _ ih (HigherHierarchy.lower_norm_le _ _)

def dropDepth (t : ℕ) (d : Fin (t+1)) : Space Y E H m t →L[ℝ] Space Y E H m (t-d.val) :=
  (dropPrefix (t-d.val) d.val).comp (castSpace (Nat.sub_add_cancel (Nat.le_of_lt_succ d.isLt)).symm)

def dropHeight (t h : ℕ) (hh : h≤t) : Space Y E H m t →L[ℝ] Space Y E H m h :=
  (dropPrefix h (t-h)).comp (castSpace (Nat.add_sub_of_le hh).symm)

theorem dropDepth_norm_le (t : ℕ) (d : Fin (t+1)) :
    ‖dropDepth (Y := Y) (E := E) (H := H) (m := m) t d‖≤1 :=
  comp_norm_le_one _ _ (dropPrefix_norm_le _ _) (castSpace_norm_le _)

theorem dropHeight_norm_le (t h : ℕ) (hh : h≤t) :
    ‖dropHeight (Y := Y) (E := E) (H := H) (m := m) t h hh‖≤1 :=
  comp_norm_le_one _ _ (dropPrefix_norm_le _ _) (castSpace_norm_le _)

def localizedProjection (t : ℕ) (d : Fin t) :
    Space Y E H m t →L[ℝ] Layer (Space Y E H m (t-(d.val+1))) (H (t-(d.val+1))) :=
  (dropPrefix (t-(d.val+1)+1) d.val).comp (castSpace (by have := d.isLt; omega))

theorem localizedProjection_norm_le (t : ℕ) (d : Fin t) :
    ‖localizedProjection (Y := Y) (E := E) (H := H) (m := m) t d‖≤1 :=
  comp_norm_le_one _ _ (dropPrefix_norm_le _ _) (castSpace_norm_le _)

def centerProjection (t : ℕ) (d : Fin t) (i : Fin 8) :
    Space Y E H m t →L[ℝ] H (t-(d.val+1)) :=
  (HigherHierarchy.parentAt (Space Y E H m (t-(d.val+1))) (H (t-(d.val+1))) i).comp
    (localizedProjection t d)

theorem centerProjection_norm_le (t : ℕ) (d : Fin t) (i : Fin 8) :
    ‖centerProjection (Y := Y) (E := E) (H := H) (m := m) t d i‖≤1 :=
  comp_norm_le_one _ _ (HigherHierarchy.parentAt_norm_le _ _ i) (localizedProjection_norm_le t d)

def oldProjection (t : ℕ) : Space Y E H m t →L[ℝ] FirstHeight.SourceSpace Y E m :=
  dropHeight t 0 (Nat.zero_le t)

def leafProjection (t : ℕ) : Space Y E H m t →L[ℝ] Leaf.Space Y E (m+1) :=
  (InnerCoordinates.numerical (Leaf.Space Y E (m+1)) E 8 (FirstHeight.depth (m+1)+2)).comp
    (oldProjection t)

theorem leafProjection_norm_le (t : ℕ) :
    ‖leafProjection (Y := Y) (E := E) (H := H) (m := m) t‖≤1 :=
  comp_norm_le_one _ _ (Inner.numerical_norm_le _ _) (dropHeight_norm_le t 0 _)

def numericalProjection (t : ℕ) : Space Y E H m t →L[ℝ] Y :=
  (InnerCoordinates.numerical Y E (m+1) (Inner.absoluteDepth+2)).comp (leafProjection t)

theorem numericalProjection_norm_le (t : ℕ) :
    ‖numericalProjection (Y := Y) (E := E) (H := H) (m := m) t‖≤1 :=
  comp_norm_le_one _ _ (Inner.numerical_norm_le _ _) (leafProjection_norm_le t)

def oldRegisterProjection (t : ℕ) (i : Fin 8) (j : Fin (FirstHeight.depth (m+1)+2)) :
    Space Y E H m t →L[ℝ] E :=
  ((PiLp.proj 2 (fun _ : Fin (FirstHeight.depth (m+1)+2) => E) j).comp
    (Inner.taskProjection (Y := Leaf.Space Y E (m+1)) (E := E) 8 (FirstHeight.depth (m+1)) i)).comp
    (oldProjection t)

theorem oldRegisterProjection_norm_le (t : ℕ) (i : Fin 8) (j : Fin (FirstHeight.depth (m+1)+2)) :
    ‖oldRegisterProjection (Y := Y) (E := E) (H := H) (m := m) t i j‖≤1 :=
  comp_norm_le_one _ _
    (comp_norm_le_one _ _ (LatchDerivativeSums.projection_norm_le j) (Inner.taskProjection_norm_le _ _ _))
    (dropHeight_norm_le t 0 _)

def innerRegisterProjection (t : ℕ) (i : Fin (m+1)) (j : Fin (Inner.absoluteDepth+2)) :
    Space Y E H m t →L[ℝ] E :=
  ((PiLp.proj 2 (fun _ : Fin (Inner.absoluteDepth+2) => E) j).comp
    (Inner.taskProjection (Y := Y) (E := E) (m+1) Inner.absoluteDepth i)).comp (leafProjection t)

theorem innerRegisterProjection_norm_le (t : ℕ) (i : Fin (m+1)) (j : Fin (Inner.absoluteDepth+2)) :
    ‖innerRegisterProjection (Y := Y) (E := E) (H := H) (m := m) t i j‖≤1 :=
  comp_norm_le_one _ _
    (comp_norm_le_one _ _ (LatchDerivativeSums.projection_norm_le j) (Inner.taskProjection_norm_le _ _ _))
    (leafProjection_norm_le t)

end Coefficients

section Raw
variable {d n r J : ℕ} {E : Type} {H : ℕ → Type}

def rawAt (h : ℕ) : (depth : ℕ) → Word depth →
    RawHierarchy.Raw d n r J E H (h+depth) → RawHierarchy.Raw d n r J E H h
  | 0,_,x => x
  | depth+1,w,x => rawAt h depth (Fin.tail w) (x.1 (w 0))

def castRaw {a b : ℕ} (h : a=b) : RawHierarchy.Raw d n r J E H a → RawHierarchy.Raw d n r J E H b :=
  _root_.cast (congrArg (RawHierarchy.Raw d n r J E H) h)

def rawAtDepth (t : ℕ) (depth : Fin (t+1)) (w : Word depth.val)
    (x : RawHierarchy.Raw d n r J E H t) : RawHierarchy.Raw d n r J E H (t-depth.val) :=
  rawAt (t-depth.val) depth.val w (castRaw (Nat.sub_add_cancel (Nat.le_of_lt_succ depth.isLt)).symm x)

def rawAtHeight (t h : ℕ) (hh : h≤t) (w : Word (t-h)) (x : RawHierarchy.Raw d n r J E H t) :
    RawHierarchy.Raw d n r J E H h :=
  rawAt h (t-h) w (castRaw (Nat.add_sub_of_le hh).symm x)

def localizedRaw (t : ℕ) (depth : Fin t) (w : Word depth.val) (x : RawHierarchy.Raw d n r J E H t) :
    RawHierarchy.Raw d n r J E H (t-(depth.val+1)+1) :=
  rawAt (t-(depth.val+1)+1) depth.val w (castRaw (by have := depth.isLt; omega) x)

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem assemble_cast (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ)
    (fallback : Fin d → ℝ) {a b : ℕ} (h : a=b) (x : RawHierarchy.Raw d n r J E H a) :
    RawHierarchy.assemble P B fallback b (castRaw h x)=castData h (RawHierarchy.assemble P B fallback a x) := by
  subst b
  rfl

theorem dataAt_assemble (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ)
    (fallback : Fin d → ℝ) (h : ℕ) : ∀ depth (w : Word depth) (x : RawHierarchy.Raw d n r J E H (h+depth)),
    dataAt h depth w (RawHierarchy.assemble P B fallback (h+depth) x)=
      RawHierarchy.assemble P B fallback h (rawAt h depth w x)
  | 0,_,_ => rfl
  | depth+1,w,x => dataAt_assemble P B fallback h depth (Fin.tail w) (x.1 (w 0))

theorem dataAtDepth_assemble (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ)
    (fallback : Fin d → ℝ) (t : ℕ) (depth : Fin (t+1)) (w : Word depth.val)
    (x : RawHierarchy.Raw d n r J E H t) :
    dataAtDepth t depth w (RawHierarchy.assemble P B fallback t x)=
      RawHierarchy.assemble P B fallback (t-depth.val) (rawAtDepth t depth w x) := by
  unfold dataAtDepth rawAtDepth
  rw [← assemble_cast]
  exact dataAt_assemble P B fallback _ _ _ _

theorem dataAtHeight_assemble (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ)
    (fallback : Fin d → ℝ) (t h : ℕ) (hh : h≤t) (w : Word (t-h))
    (x : RawHierarchy.Raw d n r J E H t) :
    dataAtHeight t h hh w (RawHierarchy.assemble P B fallback t x)=
      RawHierarchy.assemble P B fallback h (rawAtHeight t h hh w x) := by
  unfold dataAtHeight rawAtHeight
  rw [← assemble_cast]
  exact dataAt_assemble P B fallback _ _ _ _

theorem localizedData_assemble (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ)
    (fallback : Fin d → ℝ) (t : ℕ) (depth : Fin t) (w : Word depth.val)
    (x : RawHierarchy.Raw d n r J E H t) :
    localizedData t depth w (RawHierarchy.assemble P B fallback t x)=
      RawHierarchy.assemble P B fallback (t-(depth.val+1)+1) (localizedRaw t depth w x) := by
  unfold localizedData localizedRaw
  rw [← assemble_cast]
  exact dataAt_assemble P B fallback _ _ _ _

end Raw

end GradientHessian.HierarchyAddresses
