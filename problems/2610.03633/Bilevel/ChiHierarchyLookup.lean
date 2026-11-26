import Bilevel.ChiHierarchyIndex

/-! A total lookup from the source's natural-number/list indexing to the
finite legal hierarchy. Invalid indices receive no hidden random variable. -/
noncomputable section
namespace Bilevel.ChiHierarchyIndex

theorem node_key_injective {counts : ℕ → ℕ} {J : ℕ} {i k : Node counts J}
    (hlevel : i.1.val = k.1.val) (hlist : nodeList i = nodeList k) : i = k := by
  obtain ⟨i,p⟩ := i
  obtain ⟨k,q⟩ := k
  have he : i = k := Fin.ext hlevel
  subst k
  exact congrArg (Sigma.mk i) (toList_injective hlist)

open Classical in
def lookup (counts : ℕ → ℕ) (J j : ℕ) (I : List ℕ) : Option (Node counts J) :=
  if h : ∃ i : Node counts J, i.1.val = j ∧ nodeList i = I then some h.choose else none

theorem lookup_node {counts : ℕ → ℕ} {J : ℕ} (i : Node counts J) :
    lookup counts J i.1.val (nodeList i) = some i := by
  classical
  have h : ∃ k : Node counts J, k.1.val = i.1.val ∧ nodeList k = nodeList i := ⟨i,rfl,rfl⟩
  rw [lookup,dif_pos h]
  exact congrArg some (node_key_injective h.choose_spec.1 h.choose_spec.2)

theorem lookup_some_iff {counts : ℕ → ℕ} {J j : ℕ} {I : List ℕ} {i : Node counts J} :
    lookup counts J j I = some i ↔ i.1.val = j ∧ nodeList i = I := by
  classical
  constructor
  · intro he
    unfold lookup at he
    split at he
    next h =>
      have hi := Option.some.inj he
      exact hi ▸ h.choose_spec
    next h => contradiction
  · rintro ⟨rfl,rfl⟩
    exact lookup_node i

theorem lookup_exists {counts : ℕ → ℕ} {J j : ℕ} (hj : j ≤ J) (I : List ℕ)
    (hI : Legal counts I) (hlen : I.length = j+1) :
    ∃ i : Node counts J, lookup counts J j I = some i := by
  obtain ⟨i,hi,hlist⟩ := node_complete hj I hI hlen
  exact ⟨i,lookup_some_iff.mpr ⟨hi,hlist⟩⟩

theorem legal_child {counts : ℕ → ℕ} {I : List ℕ} (hI : Legal counts I)
    (i : Fin (counts I.length+1)) : Legal counts (I ++ [i.val]) := by
  have h := legal_toList (append (ofList I hI) i)
  simpa only [toList_append,toList_ofList] using h

theorem legal_macro (counts : ℕ → ℕ) (i : Fin (counts 0+1)) : Legal counts [i.val] := by
  intro j
  have hj : j.val = 0 := by have := j.isLt; simp_all
  simpa [hj] using Nat.le_of_lt_succ i.isLt

end Bilevel.ChiHierarchyIndex
