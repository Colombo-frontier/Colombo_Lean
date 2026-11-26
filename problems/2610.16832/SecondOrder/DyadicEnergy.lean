import SecondOrder.FiniteMean

open scoped BigOperators InnerProductSpace

namespace SecondOrder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
noncomputable local instance : DecidableEq E := Classical.decEq _

theorem norm_add_sq_le_twice (u v : E) : ‖u+v‖^2 ≤ 2*‖u‖^2+2*‖v‖^2 := by
  have h := norm_add_le u v
  have hn := norm_nonneg (u+v)
  nlinarith [sq_nonneg (‖u‖-‖v‖)]

theorem norm_sum_sq_le_card {ι : Type*} (s : Finset ι) (u : ι → E) :
    ‖∑ i ∈ s, u i‖^2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖u i‖^2 := by
  have hnorm := norm_sum_le s u
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1:ℝ)) (fun i => ‖u i‖)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans hcs

theorem sparse_drift_energy {ι : Type*} [DecidableEq ι] (s : Finset ι) (u : ι → E)
    (q : ℕ) (hs : (s.filter (fun i => u i ≠ 0)).card ≤ q) :
    ‖∑ i ∈ s, u i‖^2 ≤ (q:ℝ) * ∑ i ∈ s, ‖u i‖^2 := by
  classical
  let support := s.filter (fun i => u i ≠ 0)
  have heq : (∑ i ∈ support, u i) = ∑ i ∈ s, u i := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hi hnot
    simpa [support, hi] using hnot
  have heqsq : (∑ i ∈ support, ‖u i‖^2) = ∑ i ∈ s, ‖u i‖^2 := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hi hnot
    have hu : u i = 0 := by simpa [support, hi] using hnot
    simp [hu]
  have h := norm_sum_sq_le_card support u
  rw [heq, heqsq] at h
  exact h.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hs) (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

/-- Martingale isometry on a finite probability space, expressed through the
pairwise orthogonality that fresh, mean-zero signs provide. -/
theorem pmfMean_norm_sum_sq {Ω ι : Type*} [Fintype Ω] [DecidableEq ι]
    (p : PMF Ω) (s : Finset ι) (m : ι → Ω → E)
    (ho : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → pmfMean p (fun w => ⟪m i w,m j w⟫_ℝ) = 0) :
    pmfMean p (fun w => ‖∑ i ∈ s, m i w‖^2) = ∑ i ∈ s, pmfMean p (fun w => ‖m i w‖^2) := by
  induction s using Finset.induction_on with
  | empty => simp [pmfMean_const]
  | @insert i s hi ih =>
    have ho' : ∀ j ∈ s, ∀ k ∈ s, j ≠ k → pmfMean p (fun w => ⟪m j w,m k w⟫_ℝ) = 0 :=
      fun j hj k hk hne => ho j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hne
    have hc : pmfMean p (fun w => ⟪m i w, ∑ j ∈ s, m j w⟫_ℝ) = 0 := by
      simp only [inner_sum, pmfMean_finset_sum]
      apply Finset.sum_eq_zero
      intro j hj
      exact ho i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)
        (fun h => hi (h ▸ hj))
    simp only [Finset.sum_insert hi, norm_add_sq_real, pmfMean_add, pmfMean_mul,
      hc, mul_zero, add_zero, ih ho']

/-- Sum node energies using a maximum overlap count. A dyadic tree with L levels
has at most L nodes containing each time. This form avoids losing a factor q on
the martingale contribution. -/
theorem bounded_overlap_sum {ι t : Type*} [Fintype ι] [Fintype t] [DecidableEq t]
    (I : ι → Finset t) (L : ℕ) (hL : ∀ k, (Finset.univ.filter (fun i => k ∈ I i)).card ≤ L)
    (v : t → ℝ) (hv : ∀ k, 0 ≤ v k) :
    (∑ i, ∑ k ∈ I i, v k) ≤ (L:ℝ) * ∑ k, v k := by
  classical
  calc
    _ = ∑ k, ∑ i, if k ∈ I i then v k else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      simp [← Finset.sum_filter]
    _ = ∑ k, ((Finset.univ.filter (fun i => k ∈ I i)).card : ℝ) * v k := by
      apply Finset.sum_congr rfl
      intro k hk
      simp [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ k, (L:ℝ)*v k := Finset.sum_le_sum (fun k _ =>
      mul_le_mul_of_nonneg_right (by exact_mod_cast hL k) (hv k))
    _ = _ := by rw [Finset.mul_sum]

theorem drift_martingale_tree_energy {Ω ι t : Type*} [Fintype Ω] [Fintype ι]
    [Fintype t] [DecidableEq t] (p : PMF Ω) (I : ι → Finset t) (q L : ℕ)
    (a m : t → Ω → E)
    (hs : ∀ w, (Finset.univ.filter (fun k => a k w ≠ 0)).card ≤ q)
    (ho : ∀ i j, i ≠ j → pmfMean p (fun w => ⟪m i w,m j w⟫_ℝ) = 0)
    (hL : ∀ k, (Finset.univ.filter (fun i => k ∈ I i)).card ≤ L) :
    pmfMean p (fun w => ∑ i, ‖∑ k ∈ I i, (a k w+m k w)‖^2) ≤
      2*(L:ℝ)*((q:ℝ)*pmfMean p (fun w => ∑ k, ‖a k w‖^2) +
        pmfMean p (fun w => ∑ k, ‖m k w‖^2)) := by
  classical
  have hnode (i : ι) :
      pmfMean p (fun w => ‖∑ k ∈ I i, (a k w+m k w)‖^2) ≤
        2*(q:ℝ)*(∑ k ∈ I i, pmfMean p (fun w => ‖a k w‖^2)) +
        2*(∑ k ∈ I i, pmfMean p (fun w => ‖m k w‖^2)) := by
    have hb := pmfMean_mono p (fun w =>
      (show ‖∑ k ∈ I i, (a k w+m k w)‖^2 ≤
        2*(q:ℝ)*(∑ k ∈ I i, ‖a k w‖^2) + 2*‖∑ k ∈ I i, m k w‖^2 by
        rw [Finset.sum_add_distrib]
        have hd := sparse_drift_energy (I i) (fun k => a k w) q
          ((Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))).trans (hs w))
        have hn := norm_add_sq_le_twice (∑ k ∈ I i, a k w) (∑ k ∈ I i, m k w)
        linarith))
    simpa only [pmfMean_add, pmfMean_mul, pmfMean_finset_sum,
      pmfMean_norm_sum_sq p (I i) m (fun j _ k _ hne => ho j k hne)] using hb
  rw [pmfMean_finset_sum]
  have hd := bounded_overlap_sum I L hL (fun k => pmfMean p (fun w => ‖a k w‖^2))
    (fun k => pmfMean_nonneg p (fun _ => sq_nonneg _))
  have hm := bounded_overlap_sum I L hL (fun k => pmfMean p (fun w => ‖m k w‖^2))
    (fun k => pmfMean_nonneg p (fun _ => sq_nonneg _))
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hnode i)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  simp only [pmfMean_finset_sum]
  simp only [Finset.sum_add_distrib]
  nlinarith [mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ 2*(q:ℝ)),
    mul_le_mul_of_nonneg_left hm (by norm_num : (0:ℝ) ≤ 2)]

end SecondOrder
