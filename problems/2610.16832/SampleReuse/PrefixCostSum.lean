import SampleReuse.AncestorCostSum

open scoped BigOperators Classical
namespace SampleReuse
noncomputable section

theorem nat_sum_prefix_domination (N n : ℕ) (cost bound : ℕ → ℕ)
    (h : ∀ t < N, cost t ≤ if t ≤ n then bound t else 0) :
    (∑ t ∈ Finset.range N, cost t) ≤ ∑ t ∈ Finset.range (n+1), bound t := by
  calc
    _ ≤ ∑ t ∈ Finset.range N, if t ≤ n then bound t else 0 :=
      Finset.sum_le_sum (fun t ht => h t (Finset.mem_range.mp ht))
    _ = ∑ t ∈ (Finset.range N).filter (fun t => t ≤ n), bound t := by rw [Finset.sum_filter]
    _ ≤ _ := Finset.sum_le_sum_of_subset (by
      intro t ht
      have hh := (Finset.mem_filter.mp ht).2
      exact Finset.mem_range.mpr (by omega))

theorem root_and_chord_sum (n root : ℕ) (chord : ℕ → ℕ) :
    (∑ t ∈ Finset.range (n+1), if t=0 then root else 2*chord t) =
      root + 2*∑ t ∈ Finset.Icc 1 n, chord t := by
  rw [← Finset.add_sum_erase (Finset.range (n+1))
    (fun t => if t=0 then root else 2*chord t) (by simp : 0 ∈ Finset.range (n+1))]
  have he : (Finset.range (n+1)).erase 0 = Finset.Icc 1 n := by
    ext t
    simp only [Finset.mem_erase,Finset.mem_range,Finset.mem_Icc]
    omega
  rw [he,if_pos rfl]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  exact if_neg (by have := (Finset.mem_Icc.mp ht).1; omega)

end
end SampleReuse
