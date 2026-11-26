import SampleReuse.ReverseStickThirdCollision

/-! Ordered distinct-coordinate score terms have universal support multiplicity. -/

open SecondOrder
open scoped BigOperators Classical

namespace SampleReuse
noncomputable section
variable {ι : Type*} [Fintype ι]

def embeddingSupport {n : ℕ} (e : Fin n ↪ ι) : Finset ι := Finset.univ.map e

omit [Fintype ι] in
theorem embeddingSupport_card {n : ℕ} (e : Fin n ↪ ι) : (embeddingSupport e).card = n := by
  simp [embeddingSupport]

/-- An n-element support has at most n^n ordered embeddings. For the third
score this gives the sufficient universal multiplicity bound 27. -/
theorem embeddingSupport_fiber_card (n : ℕ) (s : Finset ι)
    (hs : s ∈ Finset.univ.image (@embeddingSupport ι n)) :
    (Finset.univ.filter (fun e : Fin n ↪ ι => embeddingSupport e = s)).card ≤ n ^ n := by
  obtain ⟨e₀, _, he₀⟩ := Finset.mem_image.mp hs
  have hcard : s.card = n := by rw [← he₀]; exact embeddingSupport_card e₀
  let fiber := Finset.univ.filter (fun e : Fin n ↪ ι => embeddingSupport e = s)
  let encode : ↥fiber → (Fin n → ↥s) := fun e j => ⟨e.1 j, by
    have he : embeddingSupport e.1 = s := (Finset.mem_filter.mp e.2).2
    rw [← he]
    exact Finset.mem_map.mpr ⟨j, Finset.mem_univ j, rfl⟩⟩
  have hinj : Function.Injective encode := by
    intro e f h
    apply Subtype.ext
    apply Function.Embedding.ext
    intro j
    exact congrArg Subtype.val (congrFun h j)
  have hh := Fintype.card_le_of_injective encode hinj
  simpa only [Fintype.card_coe, Fintype.card_fun, Fintype.card_fin, hcard, fiber] using hh

/-- Restricting an independent product expansion to injective coordinate
tuples only decreases a sum of nonnegative terms. -/
theorem embedding_product_sum_le (n : ℕ) (a : Fin n → ι → ℝ)
    (ha : ∀ j i, 0 ≤ a j i) :
    (∑ e : Fin n ↪ ι, ∏ j, a j (e j)) ≤ ∏ j, ∑ i, a j i := by
  let coeFun : (Fin n ↪ ι) → (Fin n → ι) := fun e => e
  have hi : Function.Injective coeFun := fun e f h => Function.Embedding.ext (congrFun h)
  calc
    _ = ∑ f ∈ Finset.univ.image coeFun, ∏ j, a j (f j) := by
      rw [Finset.sum_image (fun e _ f _ h => hi h)]
    _ ≤ ∑ f : Fin n → ι, ∏ j, a j (f j) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun f _ _ => Finset.prod_nonneg (fun j _ => ha j (f j)))
    _ = _ := (Fintype.prod_sum a).symm

/-- Product Fisher energies control the coefficient energy of all ordered
distinct-index terms. This is the analytic input after the multiplicity bound. -/
theorem embedding_fisher_energy_le
    (n : ℕ) (p : ι → ℝ) (a : Fin n → ι → ℝ)
    (hp0 : ∀ i, 0 < p i) (hp1 : ∀ i, p i < 1) :
    (∑ e : Fin n ↪ ι, (∏ j, a j (e j)) ^ 2 *
      ∏ i ∈ embeddingSupport e, (1 / (p i * (1 - p i)))) ≤
      ∏ j, bernoulliFisherEnergy p (a j) := by
  have he (e : Fin n ↪ ι) :
      (∏ j, a j (e j)) ^ 2 * (∏ i ∈ embeddingSupport e, (1 / (p i * (1 - p i)))) =
        ∏ j, (a j (e j) ^ 2 / (p (e j) * (1 - p (e j)))) := by
    simp only [embeddingSupport, Finset.prod_map, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j _
    ring
  simp only [he]
  exact embedding_product_sum_le n
    (fun j i => a j i ^ 2 / (p i * (1 - p i)))
    (fun j i => div_nonneg (sq_nonneg _) (mul_pos (hp0 i) (sub_pos.mpr (hp1 i))).le)

end
end SampleReuse
