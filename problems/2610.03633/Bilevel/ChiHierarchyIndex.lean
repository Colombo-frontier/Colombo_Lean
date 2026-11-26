import Bilevel.ChiSourceReleaseCounter
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fintype.Pi

/-! Finite indices for exactly the legal source tree. A level j node has
j+1 ancestor indices, beginning with the macro coordinate. The branching
bound for coordinate l is counts l, inclusive. -/
noncomputable section
namespace Bilevel.ChiHierarchyIndex

abbrev Path (counts : ℕ → ℕ) (length : ℕ) := ∀ i : Fin length, Fin (counts i.val+1)

def toList {counts : ℕ → ℕ} {length : ℕ} (p : Path counts length) : List ℕ :=
  List.ofFn (fun i => (p i).val)

theorem toList_length {counts : ℕ → ℕ} {length : ℕ} (p : Path counts length) :
    (toList p).length = length := List.length_ofFn

theorem toList_injective {counts : ℕ → ℕ} {length : ℕ} :
    Function.Injective (toList (counts := counts) (length := length)) := by
  intro p q h
  have he := List.ofFn_injective h
  funext i
  exact Fin.ext (congrFun he i)

def Legal (counts : ℕ → ℕ) (I : List ℕ) : Prop :=
  ∀ i : Fin I.length, I.get i ≤ counts i.val

def ofList {counts : ℕ → ℕ} (I : List ℕ) (hI : Legal counts I) : Path counts I.length :=
  fun i => ⟨I.get i,Nat.lt_succ_of_le (hI i)⟩

theorem toList_ofList {counts : ℕ → ℕ} (I : List ℕ) (hI : Legal counts I) :
    toList (ofList I hI) = I := List.ofFn_get I

theorem legal_toList {counts : ℕ → ℕ} {length : ℕ} (p : Path counts length) :
    Legal counts (toList p) := by
  intro i
  simp only [toList,List.get_ofFn]
  exact Nat.le_of_lt_succ (p (Fin.cast List.length_ofFn i)).isLt

theorem toList_cast {counts : ℕ → ℕ} {l m : ℕ} (h : l = m) (p : Path counts l) :
    toList (h ▸ p) = toList p := by
  subst m
  rfl

def append {counts : ℕ → ℕ} {length : ℕ} (p : Path counts length)
    (i : Fin (counts length+1)) : Path counts (length+1) := Fin.snoc p i

theorem toList_append {counts : ℕ → ℕ} {length : ℕ} (p : Path counts length)
    (i : Fin (counts length+1)) : toList (append p i) = toList p ++ [i.val] := by
  unfold toList append
  rw [List.ofFn_succ']
  simp

abbrev Node (counts : ℕ → ℕ) (J : ℕ) := Σ j : Fin (J+1), Path counts (j.val+1)

def nodeList {counts : ℕ → ℕ} {J : ℕ} (i : Node counts J) : List ℕ := toList i.2

theorem node_legal {counts : ℕ → ℕ} {J : ℕ} (i : Node counts J) :
    Legal counts (nodeList i) ∧ (nodeList i).length = i.1.val+1 :=
  ⟨legal_toList _,toList_length _⟩

theorem node_complete {counts : ℕ → ℕ} {J j : ℕ} (hj : j ≤ J) (I : List ℕ)
    (hI : Legal counts I) (hlen : I.length = j+1) :
    ∃ i : Node counts J, i.1.val = j ∧ nodeList i = I := by
  let p : Path counts (j+1) := hlen ▸ ofList I hI
  refine ⟨⟨⟨j,Nat.lt_succ_of_le hj⟩,p⟩,rfl,?_⟩
  change toList p = I
  exact (toList_cast hlen _).trans (toList_ofList I hI)

/-- One independent macro frame, and one frame for every legal inner node. -/
abbrev FrameIndex (counts : ℕ → ℕ) (J : ℕ) := Unit ⊕ Node counts J

def chainSize {counts : ℕ → ℕ} {J : ℕ} : FrameIndex counts J → ℕ
  | Sum.inl _ => counts 0
  | Sum.inr i => counts (i.1.val+1)

def enumerate (counts : ℕ → ℕ) (J : ℕ) :
    FrameIndex counts J ≃ Fin (Fintype.card (FrameIndex counts J)) := Fintype.equivFin _

theorem frame_count_positive (counts : ℕ → ℕ) (J : ℕ) :
    0 < Fintype.card (FrameIndex counts J) := by
  exact Fintype.card_pos_iff.mpr ⟨Sum.inl ()⟩

end Bilevel.ChiHierarchyIndex
