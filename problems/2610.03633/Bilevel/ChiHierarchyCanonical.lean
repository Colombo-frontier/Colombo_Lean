import Bilevel.ChiHierarchyLookup

/-! Public canonicalization of arbitrary list indices to legal paths.
Both frames and retained counts can use this same map. It preserves every
legal path and commutes with appending a valid child index. -/
noncomputable section
namespace Bilevel.ChiHierarchyIndex

def canonicalPath (counts : ℕ → ℕ) : (length : ℕ) → List ℕ → Path counts length
  | 0,_ => fun i => Fin.elim0 i
  | length+1,I => append (canonicalPath counts length I.dropLast)
      ⟨I.getLastD 0 % (counts length+1),Nat.mod_lt _ (Nat.succ_pos _)⟩

def canonicalList (counts : ℕ → ℕ) (length : ℕ) (I : List ℕ) : List ℕ :=
  toList (canonicalPath counts length I)

theorem canonicalPath_append (counts : ℕ → ℕ) (length : ℕ) (I : List ℕ)
    (i : Fin (counts length+1)) :
    canonicalPath counts (length+1) (I ++ [i.val]) = append (canonicalPath counts length I) i := by
  have hlast : (I ++ [i.val]).getLastD 0 = i.val := List.getLastD_concat
  simp only [canonicalPath,List.dropLast_append_cons,List.dropLast_single,List.append_nil,
    hlast,Nat.mod_eq_of_lt i.isLt]

theorem canonicalList_append (counts : ℕ → ℕ) (length : ℕ) (I : List ℕ)
    (i : Fin (counts length+1)) :
    canonicalList counts (length+1) (I ++ [i.val]) = canonicalList counts length I ++ [i.val] := by
  rw [canonicalList,canonicalPath_append,toList_append]
  rfl

theorem canonicalPath_toList {counts : ℕ → ℕ} {length : ℕ} (p : Path counts length) :
    canonicalPath counts length (toList p) = p := by
  induction length with
  | zero => exact Subsingleton.elim _ _
  | succ length ih =>
    have he : toList p = toList (fun i : Fin length => p i.castSucc) ++ [(p (Fin.last length)).val] := by
      unfold toList
      simpa only [List.concat_eq_append] using List.ofFn_succ' (fun k => (p k).val)
    rw [he,canonicalPath_append,ih]
    exact Fin.snoc_init_self p

theorem canonicalList_toList {counts : ℕ → ℕ} {length : ℕ} (p : Path counts length) :
    canonicalList counts length (toList p) = toList p := by
  rw [canonicalList,canonicalPath_toList]

theorem canonicalList_legal (counts : ℕ → ℕ) (length : ℕ) (I : List ℕ) :
    Legal counts (canonicalList counts length I) := legal_toList _

theorem canonicalList_length (counts : ℕ → ℕ) (length : ℕ) (I : List ℕ) :
    (canonicalList counts length I).length = length := toList_length _

theorem canonicalList_id {counts : ℕ → ℕ} (I : List ℕ) (hI : Legal counts I) :
    canonicalList counts I.length I = I := by
  simpa only [toList_ofList] using canonicalList_toList (ofList I hI)

def canonicalNode (counts : ℕ → ℕ) (J : ℕ) (j : Fin (J+1)) (I : List ℕ) : Node counts J :=
  ⟨j,canonicalPath counts (j.val+1) I⟩

theorem canonicalNode_at_node {counts : ℕ → ℕ} {J : ℕ} (i : Node counts J) :
    canonicalNode counts J i.1 (nodeList i) = i := by
  obtain ⟨j,p⟩ := i
  simp only [canonicalNode,nodeList,canonicalPath_toList]

end Bilevel.ChiHierarchyIndex
