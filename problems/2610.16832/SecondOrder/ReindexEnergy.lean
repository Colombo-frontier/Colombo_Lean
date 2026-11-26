import SecondOrder.PredictableReindex

open scoped Classical BigOperators

namespace SecondOrder
noncomputable section

/-- Injective relabeling has at most one physical vector at each address. -/
theorem norm_sum_injective_fiber_sq {I R E : Type*} [Fintype I]
    [NormedAddCommGroup E] (label : I → R) (hl : Function.Injective label) (x : I → E) (r : R) :
    ‖∑ i, if label i=r then x i else 0‖^2 = ∑ i, if label i=r then ‖x i‖^2 else 0 := by
  by_cases he : ∃ i, label i=r
  · obtain ⟨i,hi⟩ := he
    have hs (j : I) (hj : j ≠ i) : label j ≠ r := fun hh => hj (hl (hh.trans hi.symm))
    have hx : (∑ j, if label j=r then x j else 0) = x i := by
      rw [Finset.sum_eq_single i]
      · simp [hi]
      · intro j hj hji
        simp [hs j hji]
      · simp
    have hy : (∑ j, if label j=r then ‖x j‖^2 else 0) = ‖x i‖^2 := by
      rw [Finset.sum_eq_single i]
      · simp [hi]
      · intro j hj hji
        simp [hs j hji]
      · simp
    rw [hx,hy]
  · have hn (i : I) : label i ≠ r := fun hh => he ⟨i,hh⟩
    simp [hn]

/-- Summing over a finite set of addresses that contains every physical
address exactly preserves the total squared increment energy. -/
theorem sum_injective_fiber_energy {I R E : Type*} [Fintype I]
    [NormedAddCommGroup E] (label : I → R) (hl : Function.Injective label) (x : I → E)
    (s : Finset R) (hs : ∀ i, label i ∈ s) :
    (∑ r ∈ s, ‖∑ i, if label i=r then x i else 0‖^2) = ∑ i, ‖x i‖^2 := by
  simp_rw [norm_sum_injective_fiber_sq label hl x]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single (label i)]
  · simp
  · intro r hr hri
    simp [hri.symm]
  · exact fun hh => False.elim (hh (hs i))

end
end SecondOrder
