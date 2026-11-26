import SecondOrder.LocalTensors

open scoped BigOperators Classical

namespace SecondOrder
noncomputable section

variable {J I : Type*} [Fintype J] [Fintype I] (E : J → Type*)
  [∀ j, NormedAddCommGroup (E j)] [∀ j, NormedSpace ℝ (E j)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  (S : I → Finset J)

/-- The actual sum of local functions, each evaluated only on its coordinate blocks. -/
def localObjective (φ : ∀ i, LocalBlockSpace E (S i) → F) (x : BlockSpace E) : F :=
  ∑ i, φ i (blockRestrict E (S i) x)

theorem localObjective_contDiff {k : ℕ} (φ : ∀ i, LocalBlockSpace E (S i) → F)
    (hφ : ∀ i, ContDiff ℝ k (φ i)) : ContDiff ℝ k (localObjective E S φ) :=
  ContDiff.sum (fun i _ => (hφ i).comp (blockRestrict E (S i)).contDiff)

/-- The local tensor sum is proved equal to the genuine iterated Fréchet derivative. -/
theorem iteratedFDeriv_localObjective {k : ℕ} (φ : ∀ i, LocalBlockSpace E (S i) → F)
    (hφ : ∀ i, ContDiff ℝ k (φ i)) (x : BlockSpace E) :
    iteratedFDeriv ℝ k (localObjective E S φ) x =
      localTensorSum E S (fun i => iteratedFDeriv ℝ k (φ i) (blockRestrict E (S i) x)) := by
  unfold localObjective localTensorSum
  rw [iteratedFDeriv_sum (u := Finset.univ)
    (f := fun i x => φ i (blockRestrict E (S i) x))
    (fun i _ => (hφ i).comp (blockRestrict E (S i)).contDiff)]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact (blockRestrict E (S i)).iteratedFDeriv_comp_right (hφ i) x le_rfl

/-- The second-order conclusion of the manuscript's bounded-degree local-tensor lemma. -/
theorem localObjective_second_bound (r : ℕ)
    (hr : ∀ j, (Finset.univ.filter (fun i => j ∈ S i)).card ≤ r)
    (φ : ∀ i, LocalBlockSpace E (S i) → F) (hφ : ∀ i, ContDiff ℝ 2 (φ i))
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ i y, ‖iteratedFDeriv ℝ 2 (φ i) y‖ ≤ M)
    (x : BlockSpace E) : ‖iteratedFDeriv ℝ 2 (localObjective E S φ) x‖ ≤ (r:ℝ)*M := by
  rw [iteratedFDeriv_localObjective E S φ hφ]
  exact localTensorSum_two_bound E S r hr _ hM (fun i => hbound i _)

/-- The third-order conclusion, with the same multiplicity r and no chain-length factor. -/
theorem localObjective_third_bound (r : ℕ)
    (hr : ∀ j, (Finset.univ.filter (fun i => j ∈ S i)).card ≤ r)
    (φ : ∀ i, LocalBlockSpace E (S i) → F) (hφ : ∀ i, ContDiff ℝ 3 (φ i))
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ i y, ‖iteratedFDeriv ℝ 3 (φ i) y‖ ≤ M)
    (x : BlockSpace E) : ‖iteratedFDeriv ℝ 3 (localObjective E S φ) x‖ ≤ (r:ℝ)*M := by
  rw [iteratedFDeriv_localObjective E S φ hφ]
  exact localTensorSum_three_bound E S r hr _ hM (fun i => hbound i _)

end
end SecondOrder
