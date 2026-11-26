import SampleReuse.AncestorNodes

open SecondOrder
open scoped BigOperators Classical
namespace SampleReuse
noncomputable section

/-- The sparse useful-node sum is exactly one ancestor chord per positive
checkpoint, including a final inspection checkpoint when it is present. -/
theorem selected_ancestor_sum {A : Type*} [AddCommMonoid A]
    (depth M n : ℕ) (hn : n ≤ M) (hd : n < 2^depth) (weight : ℕ → ℕ → A) :
    (∑ i ∈ Finset.univ.filter (fun i : completedNodes depth M => usefulNode i.val ∧ nodeRight i.val ≤ n),
      weight (nodeRight i.val) (nodeLeft i.val)) =
        ∑ k ∈ Finset.Icc 1 n, weight k (ancestorParent k) := by
  apply Finset.sum_bij (fun (i : completedNodes depth M) _ => nodeRight i.val)
  · intro i hi
    exact Finset.mem_Icc.mpr ⟨nodeRight_pos i.val,(Finset.mem_filter.mp hi).2.2⟩
  · intro i hi j hj hij
    apply Subtype.ext
    exact usefulNode_right_injective (Finset.mem_filter.mp hi).2.1
      (Finset.mem_filter.mp hj).2.1 hij
  · intro k hk
    have hk' := Finset.mem_Icc.mp hk
    let a := ancestorNode k hk'.1 (hk'.2.trans_lt hd)
    have ha : a ∈ completedNodes depth M := by
      apply (mem_completedNodes a).mpr
      rw [ancestorNode_right]
      exact hk'.2.trans hn
    refine ⟨⟨a,ha⟩,?_,?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,ancestorNode_useful k hk'.1 (hk'.2.trans_lt hd),by
        simpa only [a,ancestorNode_right] using hk'.2⟩
    · exact ancestorNode_right k hk'.1 (hk'.2.trans_lt hd)
  · intro i hi
    rw [usefulNode_parent _ (Finset.mem_filter.mp hi).2.1]

end
end SampleReuse
