import SignVector254

noncomputable section
open scoped BigOperators
namespace Paper254

theorem block_mod_count (m n t : ℕ) (hm : 0 < m) (hn : 0 < n) :
    ((Finset.univ : Finset (Fin t)).filter (fun i => i.val/(n*m) = t/(n*m) ∧ i.val%m = t%m)).card ≤ n := by
  let L := n*m
  have hL : 0 < L := Nat.mul_pos hn hm
  let src := (Finset.univ : Finset (Fin t)).filter (fun i => i.val/L = t/L ∧ i.val%m = t%m)
  let f := fun i : Fin t => (i.val%L)/m
  have hmap : Set.MapsTo f src (Finset.range n) := by
    intro i _
    apply Finset.mem_range.mpr
    exact (Nat.div_lt_iff_lt_mul hm).mpr (Nat.mod_lt i.val hL)
  have hinj : Set.InjOn f src := by
    intro i hi j hj he
    have hi' := (Finset.mem_filter.mp hi).2
    have hj' := (Finset.mem_filter.mp hj).2
    have hqi : i.val/L = j.val/L := hi'.1.trans hj'.1.symm
    have hmi : i.val%m = j.val%m := hi'.2.trans hj'.2.symm
    have hd : m ∣ L := by dsimp [L]; exact dvd_mul_left m n
    have h1 := Nat.mod_add_div (i.val%L) m
    have h2 := Nat.mod_add_div (j.val%L) m
    rw [Nat.mod_mod_of_dvd _ hd] at h1 h2
    change (i.val%L)/m = (j.val%L)/m at he
    rw [he,hmi] at h1
    have hr : i.val%L = j.val%L := by omega
    have h3 := Nat.mod_add_div i.val L
    have h4 := Nat.mod_add_div j.val L
    rw [hqi,hr] at h3
    exact Fin.ext (by omega)
  have hc := Finset.card_le_card_of_injOn f hmap hinj
  simpa only [Finset.card_range] using hc

theorem block_mod_information (m n t : ℕ) (hm : 0 < m) (hn : 0 < n) (θ : ℝ) :
    (∑ i : Fin t, if i.val/(n*m) = t/(n*m) ∧ i.val%m = t%m then θ^2 else 0) ≤ (n : ℝ)*θ^2 := by
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul]
  have hc : ((((Finset.univ : Finset (Fin t)).filter
      (fun i => i.val/(n*m) = t/(n*m) ∧ i.val%m = t%m)).card : ℝ)) ≤ n := by
    exact_mod_cast block_mod_count m n t hm hn
  exact mul_le_mul_of_nonneg_right hc (sq_nonneg θ)

def blockIndex (K n m : ℕ) (hK : 0 < K) (t : ℕ) : Fin K :=
  ⟨min (t/(n*m)) (K-1), lt_of_le_of_lt (min_le_right _ _) (by omega)⟩

theorem blockIndex_monotone (K n m : ℕ) (hK : 0 < K) : Monotone (blockIndex K n m hK) := by
  intro i j hij
  change min (i/(n*m)) (K-1) ≤ min (j/(n*m)) (K-1)
  exact min_le_min_right _ (Nat.div_le_div_right hij)

theorem blockIndex_before_end (K n m t : ℕ) (hK : 0 < K) (hn : 0 < n) (hm : 0 < m)
    (ht : t < K*(n*m)) : (blockIndex K n m hK t).val = t/(n*m) := by
  have hh : t/(n*m) < K := (Nat.div_lt_iff_lt_mul (Nat.mul_pos hn hm)).mpr ht
  exact min_eq_left (by omega)

end Paper254
#print axioms Paper254.block_mod_information
