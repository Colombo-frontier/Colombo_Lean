import SampleReuse.ReverseStickThirdOrderedScore
import SampleReuse.ReverseStickThirdDensity

open SecondOrder
open scoped BigOperators Classical
namespace SampleReuse
noncomputable section
variable {ι : Type*} [Fintype ι]

theorem sum_embeddings_eq_injective (n : ℕ) (F : (Fin n → ι) → ℝ) :
    (∑ e : Fin n ↪ ι, F e) =
      ∑ f : Fin n → ι, if Function.Injective f then F f else 0 := by
  rw [← (Equiv.subtypeInjectiveEquivEmbedding (Fin n) ι).sum_comp]
  simp only [Equiv.subtypeInjectiveEquivEmbedding]
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (fun _ => by simp) F).symm

theorem sum_fun_two (F : (Fin 2 → ι) → ℝ) :
    (∑ f, F f) = ∑ i, ∑ j, F ![i, j] := by
  rw [← (finTwoArrowEquiv ι).symm.sum_comp]
  rw [Fintype.sum_prod_type]
  rfl

theorem sum_fun_three (F : (Fin 3 → ι) → ℝ) :
    (∑ f, F f) = ∑ i, ∑ j, ∑ k, F ![i, j, k] := by
  rw [← (Fin.consEquiv (fun _ : Fin 3 => ι)).sum_comp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  exact sum_fun_two (fun f => F (Fin.cons i f))

omit [Fintype ι] in
theorem injective_pair (i j : ι) : Function.Injective ![i, j] ↔ i ≠ j := by
  constructor
  · intro h hij
    have hh := h (show (![i, j] : Fin 2 → ι) 0 = ![i, j] 1 from hij)
    exact (by decide : (0 : Fin 2) ≠ 1) hh
  · intro hij a b hab
    fin_cases a <;> fin_cases b <;> simp_all

omit [Fintype ι] in
theorem injective_triple (i j k : ι) :
    Function.Injective ![i, j, k] ↔ i ≠ j ∧ i ≠ k ∧ j ≠ k := by
  constructor
  · intro h
    exact ⟨fun he => (by decide : (0 : Fin 3) ≠ 1) (h he),
      fun he => (by decide : (0 : Fin 3) ≠ 2) (h he),
      fun he => (by decide : (1 : Fin 3) ≠ 2) (h he)⟩
  · rintro ⟨hij, hik, hjk⟩ a b hab
    fin_cases a <;> fin_cases b <;> simp_all

def orderedCoordinateProduct (n : ℕ) (a : Fin n → ι → ℝ) : ℝ :=
  ∑ e : Fin n ↪ ι, ∏ j, a j (e j)

theorem orderedCoordinateProduct_two (a b : ι → ℝ) :
    orderedCoordinateProduct 2 ![a, b] =
      (∑ i, a i) * (∑ i, b i) - ∑ i, a i * b i := by
  rw [orderedCoordinateProduct,
    sum_embeddings_eq_injective 2 (fun f => ∏ j, ![a, b] j (f j)), sum_fun_two]
  simp only [injective_pair, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  have he (i j : ι) : (if i ≠ j then a i * b j else 0) =
      a i * b j - if i = j then a i * b j else 0 := by
    split_ifs <;> simp_all
  simp_rw [he, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [← Finset.sum_mul_sum]

theorem orderedCoordinateProduct_three (a b c : ι → ℝ) :
    orderedCoordinateProduct 3 ![a, b, c] =
      (∑ i, a i) * (∑ i, b i) * (∑ i, c i) -
      (∑ i, a i * b i) * (∑ i, c i) -
      (∑ i, a i * c i) * (∑ i, b i) -
      (∑ i, b i * c i) * (∑ i, a i) + 2 * ∑ i, a i * b i * c i := by
  rw [orderedCoordinateProduct,
    sum_embeddings_eq_injective 3 (fun f => ∏ j, ![a, b, c] j (f j)), sum_fun_three]
  simp only [injective_triple, Fin.prod_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons]
  have he (i j k : ι) :
      (if i ≠ j ∧ i ≠ k ∧ j ≠ k then a i * b j * c k else 0) =
      a i * b j * c k - (if i = j then a i * b j * c k else 0) -
      (if i = k then a i * b j * c k else 0) -
      (if j = k then a i * b j * c k else 0) +
      2 * (if i = j ∧ j = k then a i * b j * c k else 0) := by
    by_cases hij : i = j <;> by_cases hik : i = k <;> by_cases hjk : j = k <;>
      simp_all
    all_goals ring
  simp only [he, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have ht : (∑ i, ∑ j, ∑ k, a i * b j * c k) =
      (∑ i, a i) * (∑ i, b i) * (∑ i, c i) := by
    calc
      _ = ∑ i, ∑ j, (a i * b j) * ∑ k, c k := by simp only [Finset.mul_sum]
      _ = (∑ i, ∑ j, a i * b j) * ∑ k, c k := by simp only [Finset.sum_mul]
      _ = _ := by rw [← Finset.sum_mul_sum]
  have hij : (∑ i, ∑ j, ∑ k, if i = j then a i * b j * c k else 0) =
      (∑ i, a i * b i) * (∑ i, c i) := by
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    exact (Finset.sum_mul_sum _ _ _ _).symm
  have hik : (∑ i, ∑ j, ∑ k, if i = k then a i * b j * c k else 0) =
      (∑ i, a i * c i) * (∑ i, b i) := by
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hjk : (∑ i, ∑ j, ∑ k, if j = k then a i * b j * c k else 0) =
      (∑ i, b i * c i) * (∑ i, a i) := by
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [mul_comm, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hijk : (∑ i, ∑ j, ∑ k, if i = j ∧ j = k then a i * b j * c k else 0) =
      ∑ i, a i * b i * c i := by
    simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hijk2 : (∑ i, ∑ j, ∑ k, 2 * (if i = j ∧ j = k then a i * b j * c k else 0)) =
      2 * ∑ i, a i * b i * c i := by
    simp only [← Finset.mul_sum]
    rw [hijk]
  rw [ht, hij, hik, hjk, hijk2]

theorem orderedBernoulliScore_eq_coordinateProduct
    (n : ℕ) (p : ι → ℝ) (a : Fin n → ι → ℝ) (w : ι → Bool) :
    orderedBernoulliScore n p a w =
      orderedCoordinateProduct n (fun j i => a j i * binaryScore (p i) (w i)) := by
  unfold orderedBernoulliScore orderedCoordinateProduct
  apply Finset.sum_congr rfl
  intro e _
  simp only [scoreMonomial, embeddingSupport, Finset.prod_map, Finset.prod_mul_distrib]

end
end SampleReuse
