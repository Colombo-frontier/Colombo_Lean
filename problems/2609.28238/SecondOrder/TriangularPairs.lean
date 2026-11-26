import SecondOrder.EuclideanCoordinates

open scoped BigOperators Classical

namespace SecondOrder
noncomputable section

abbrev UpperPair (d : ℕ) := {p : Fin d × Fin d // p.1 < p.2}

theorem sum_upperPair {d : ℕ} (F : Fin d → Fin d → ℝ) :
    (∑ e : UpperPair d, F e.1.1 e.1.2) = ∑ i, ∑ j, if i < j then F i j else 0 := by
  rw [← Finset.sum_subtype (Finset.univ.filter (fun p : Fin d × Fin d => p.1 < p.2))
    (by intro p; simp) (fun p => F p.1 p.2)]
  rw [Finset.sum_filter, Fintype.sum_prod_type]

/-- A symmetric matrix sum splits into its diagonal and twice its upper triangle. -/
theorem symmetric_sum_pairs {d : ℕ} (F : Fin d → Fin d → ℝ)
    (hF : ∀ i j, F i j = F j i) :
    (∑ i, ∑ j, F i j) = (∑ i, F i i)+2*∑ e : UpperPair d, F e.1.1 e.1.2 := by
  have he (i j : Fin d) : F i j =
      (if i = j then F i i else 0)+(if i < j then F i j else 0)+(if j < i then F j i else 0) := by
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h, h.ne, not_lt.mpr h.le]
    · simp
    · simp [h, h.ne', not_lt.mpr h.le, hF i j]
  have hs : (∑ i, ∑ j, if j < i then F j i else 0) = ∑ i, ∑ j, if i < j then F i j else 0 :=
    Finset.sum_comm
  calc
    _ = ∑ i, ∑ j, ((if i = j then F i i else 0)+
        (if i < j then F i j else 0)+(if j < i then F j i else 0)) := by
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      exact he i j
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [hs, sum_upperPair]
      ring

theorem upperPair_card_real (d : ℕ) : (Fintype.card (UpperPair d):ℝ) = (d:ℝ)*((d:ℝ)-1)/2 := by
  have h := symmetric_sum_pairs (d := d) (fun _ _ => 1) (fun _ _ => rfl)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h
  nlinarith

theorem pair_difference_identity {d : ℕ} (v : Point d) :
    (∑ e : UpperPair d, (v e.1.1-v e.1.2)^2) = (d:ℝ)*‖v‖^2-(∑ i, v i)^2 := by
  have h := symmetric_sum_pairs (fun i j => (v i-v j)^2) (fun i j => by ring)
  simp only [sub_self, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero, zero_add] at h
  have he : (∑ i, ∑ j, (v i-v j)^2) = 2*(d:ℝ)*‖v‖^2-2*(∑ i, v i)^2 := by
    simp_rw [sub_sq]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul,
      ← euclidean_norm_sq]
    ring
  linarith

theorem pair_difference_sq_sum_le {d : ℕ} (v : Point d) :
    (∑ e : UpperPair d, (v e.1.1-v e.1.2)^2) ≤ (d:ℝ)*‖v‖^2 := by
  rw [pair_difference_identity]
  exact sub_le_self _ (sq_nonneg _)

end
end SecondOrder
