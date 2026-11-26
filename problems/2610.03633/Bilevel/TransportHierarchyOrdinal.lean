import Bilevel.ChiHierarchyCanonical
import Bilevel.ChiHierarchyReleaseCounter
import Bilevel.TransportRoundPrefix

/-! Exact lexicographic terminal-column indices. The actual recursive prefix
counter is the restriction of one global prefix, which is the frame carried
by the endpoint network. -/
noncomputable section
namespace Bilevel.TransportHierarchy
open ChiTreeProgress ChiHierarchyIndex

def LegalFrom (counts : ℕ → ℕ) : ℕ → List ℕ → Prop
  | _,[] => True
  | j,i::I => i<counts j+1 ∧ LegalFrom counts (j+1) I

theorem legalFrom_of_get (counts : ℕ → ℕ) (j : ℕ) (I : List ℕ)
    (h : ∀ i : Fin I.length,I.get i≤counts (j+i.val)) : LegalFrom counts j I := by
  induction I generalizing j with
  | nil => trivial
  | cons a I ih =>
    constructor
    · have hh := h ⟨0,by simp⟩
      simpa only [List.get_cons_zero,Fin.val_zero,Nat.add_zero,Nat.lt_succ_iff] using hh
    · apply ih
      intro i
      have hh := h i.succ
      simpa only [List.get_cons_succ,Fin.val_succ,Nat.add_assoc,Nat.add_comm 1 i.val] using hh

theorem canonical_legalFrom (counts : ℕ → ℕ) (d : ℕ) (I : List ℕ) :
    LegalFrom counts 0 (canonicalList counts d I) := by
  apply legalFrom_of_get
  intro i
  simpa only [Nat.zero_add] using canonicalList_legal counts d I i

def offset (counts : ℕ → ℕ) : ℕ → ℕ → List ℕ → ℕ
  | _,_,[] => 0
  | d,j,i::I => i*capacity counts (d-1) (j+1)+offset counts (d-1) (j+1) I

theorem offset_column_lt (counts : ℕ → ℕ) (d j : ℕ) (I : List ℕ)
    (hI : I.length=d) (hlegal : LegalFrom counts j I) (k : ℕ) (hk : k<counts (j+d)+1) :
    offset counts d j I+k<capacity counts d j := by
  induction I generalizing d j with
  | nil =>
    have hd : d=0 := by simpa using hI.symm
    subst d
    simpa only [offset,capacity,Nat.zero_add,Nat.add_zero] using hk
  | cons i I ih =>
    have hd : d≠0 := by simp only [List.length_cons] at hI;omega
    obtain ⟨d,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd
    have hlen : I.length=d := by simp only [List.length_cons] at hI;omega
    have hkl : k<counts ((j+1)+d)+1 := by
      convert hk using 1
      congr 2
      omega
    have hh := ih d (j+1) hlen hlegal.2 hkl
    have hm := Nat.mul_le_mul_right (capacity counts d (j+1)) (Nat.succ_le_iff.mpr hlegal.1)
    simp only [offset,Nat.succ_sub_one,capacity]
    nlinarith only [hh,hm]

theorem nodeBudget_column_iff (counts : ℕ → ℕ) (d j q : ℕ) (I : List ℕ)
    (hI : I.length=d) (hlegal : LegalFrom counts j I) (k : ℕ) (hk : k<counts (j+d)+1) :
    k<nodeBudget counts d j q I ↔ offset counts d j I+k<q := by
  induction I generalizing d j q with
  | nil =>
    simp only [nodeBudget,offset,Nat.zero_add]
  | cons i I ih =>
    have hd : d≠0 := by simp only [List.length_cons] at hI;omega
    obtain ⟨d,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd
    have hlen : I.length=d := by simp only [List.length_cons] at hI;omega
    have hkl : k<counts ((j+1)+d)+1 := by
      convert hk using 1
      congr 2
      omega
    have hbound := offset_column_lt counts d (j+1) I hlen hlegal.2 k hkl
    simp only [nodeBudget,offset,Nat.succ_sub_one]
    rw [ih d (j+1) _ hlen hlegal.2 hkl]
    simp only [childBudget,lt_min_iff,hbound,true_and]
    omega

def terminalIndex (counts : ℕ → ℕ) (d : ℕ) (I : List ℕ)
    (hI : I.length=d) (hlegal : LegalFrom counts 0 I) (k : Fin (counts d+1)) :
    Fin (capacity counts d 0) :=
  ⟨offset counts d 0 I+k.val,offset_column_lt counts d 0 I hI hlegal k.val (by rw [Nat.zero_add];exact k.isLt)⟩

theorem terminalIndex_injective (counts : ℕ → ℕ) (d : ℕ) (I : List ℕ)
    (hI : I.length=d) (hlegal : LegalFrom counts 0 I) :
    Function.Injective (terminalIndex counts d I hI hlegal) := by
  intro k l h
  apply Fin.ext
  have hh := congrArg Fin.val h
  exact Nat.add_left_cancel hh

theorem counter_column_iff (counts : ℕ → ℕ) (d q : ℕ) (I : List ℕ)
    (hI : I.length=d) (hlegal : LegalFrom counts 0 I) (k : Fin (counts d+1)) :
    k.val<counter counts d q d I ↔ (terminalIndex counts d I hI hlegal k).val<q := by
  rw [counter_at counts d q d I hI]
  simp only [Nat.sub_self,nodePrefix,lt_min_iff,k.isLt,true_and]
  exact nodeBudget_column_iff counts d 0 q I hI hlegal k.val (by rw [Nat.zero_add];exact k.isLt)

theorem source_protected_iff {n : ℕ} (hn : 0<n) (counts : ℕ → ℕ) (d t : ℕ) (I : List ℕ)
    (hI : I.length=d) (hlegal : LegalFrom counts 0 I) (k : Fin (counts d+1)) :
    TransportRound.Protected t (0 : TransportNetwork.Vertex n) (terminalIndex counts d I hI hlegal k) ↔
      k.val<counter counts d (t/n+1) d I := by
  rw [counter_column_iff]
  change (terminalIndex counts d I hI hlegal k).val*n+0≤t ↔ _
  rw [Nat.add_zero,←Nat.le_div_iff_mul_le hn]
  omega

theorem target_protected_iff {n : ℕ} (hn : 0<n) (counts : ℕ → ℕ) (d t : ℕ) (I : List ℕ)
    (hI : I.length=d) (hlegal : LegalFrom counts 0 I) (k : Fin (counts d+1)) :
    TransportRound.Protected t (Fin.last n) (terminalIndex counts d I hI hlegal k) ↔
      k.val<counter counts d (t/n) d I := by
  rw [TransportRound.completed_prefix hn,counter_column_iff]
  omega

end Bilevel.TransportHierarchy
