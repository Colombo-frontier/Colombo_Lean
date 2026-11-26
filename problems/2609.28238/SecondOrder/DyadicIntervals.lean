import SecondOrder.DyadicEnergy

open scoped BigOperators InnerProductSpace Classical

namespace SecondOrder
noncomputable section

/-- The deterministic padded partition at level `l`. Empty intervals are harmless. -/
def dyadicBlock (M l : ℕ) (j : Fin M) : Finset (Fin M) :=
  Finset.univ.filter (fun t => t.val / 2^l = j.val)

theorem dyadic_overlap {L M : ℕ} (t : Fin M) :
    (Finset.univ.filter (fun i : Fin L × Fin M => t ∈ dyadicBlock M i.1.val i.2)).card ≤ L := by
  let index : Fin L → Fin M := fun l =>
    ⟨t.val / 2^l.val, lt_of_le_of_lt (Nat.div_le_self _ _) t.isLt⟩
  have heq : Finset.univ.filter (fun i : Fin L × Fin M => t ∈ dyadicBlock M i.1.val i.2) =
      Finset.univ.image (fun l => (l,index l)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hi
      refine ⟨i.1, ?_⟩
      apply Prod.ext
      · rfl
      · apply Fin.ext
        exact (Finset.mem_filter.mp hi).2
    · rintro ⟨l, rfl⟩
      simp [dyadicBlock, index]
  rw [heq]
  exact (Finset.card_image_le).trans_eq (by simp)

/-- The exact constant 2 in the finite-probability version of the paper's tree
energy lemma. Orthogonality remains an explicit hypothesis at this layer. -/
theorem dyadic_energy {Ω E : Type*} [Fintype Ω] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (p : PMF Ω) (M L q : ℕ)
    (a m : Fin M → Ω → E)
    (hs : ∀ w, (Finset.univ.filter (fun k => a k w ≠ 0)).card ≤ q)
    (ho : ∀ i j, i ≠ j → pmfMean p (fun w => ⟪m i w,m j w⟫_ℝ) = 0) :
    pmfMean p (fun w => ∑ i : Fin L × Fin M,
      ‖∑ k ∈ dyadicBlock M i.1.val i.2, (a k w+m k w)‖^2) ≤
      2*(L:ℝ)*((q:ℝ)*pmfMean p (fun w => ∑ k, ‖a k w‖^2) +
        pmfMean p (fun w => ∑ k, ‖m k w‖^2)) := by
  exact drift_martingale_tree_energy p (fun i : Fin L × Fin M => dyadicBlock M i.1.val i.2)
    q L a m hs ho dyadic_overlap

/-- Selection of completed nodes is bounded pointwise before taking expectations;
no conditioning on a future-dependent completion event is used. -/
theorem selected_dyadic_energy {Ω E : Type*} [Fintype Ω] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (p : PMF Ω) (M L q : ℕ)
    (a m : Fin M → Ω → E)
    (created : Ω → Fin L × Fin M → Prop) [∀ w i, Decidable (created w i)]
    (hs : ∀ w, (Finset.univ.filter (fun k => a k w ≠ 0)).card ≤ q)
    (ho : ∀ i j, i ≠ j → pmfMean p (fun w => ⟪m i w,m j w⟫_ℝ) = 0) :
    pmfMean p (fun w => ∑ i : Fin L × Fin M, if created w i then
      ‖∑ k ∈ dyadicBlock M i.1.val i.2, (a k w+m k w)‖^2 else 0) ≤
      2*(L:ℝ)*((q:ℝ)*pmfMean p (fun w => ∑ k, ‖a k w‖^2) +
        pmfMean p (fun w => ∑ k, ‖m k w‖^2)) := by
  apply le_trans (pmfMean_mono p ?_) (dyadic_energy p M L q a m hs ho)
  intro w
  apply Finset.sum_le_sum
  intro i hi
  split_ifs <;> simp [sq_nonneg]

end
end SecondOrder
