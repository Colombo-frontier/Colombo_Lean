import AnytimeSchedule254

noncomputable section
open scoped BigOperators
namespace Paper254

theorem epoch_curved_sum {ι : Type*} (s : Finset ι) (H P : ι → ℝ)
    (hH : ∀ j ∈ s, 0 ≤ H j) (hP : ∀ j ∈ s, 0 ≤ P j) :
    (∑ j ∈ s,(H j)^(1/3:ℝ)*(P j)^(2/3:ℝ)) ≤
      (∑ j ∈ s,H j)^(1/3:ℝ)*(∑ j ∈ s,P j)^(2/3:ℝ) := by
  have hc : Real.HolderConjugate 3 (3/2) := by norm_num [Real.holderConjugate_iff]
  have hh := Real.inner_le_Lp_mul_Lq_of_nonneg s (f := fun j => (H j)^(1/3:ℝ))
    (g := fun j => (P j)^(2/3:ℝ)) hc
    (fun j hj => Real.rpow_nonneg (hH j hj) _)
    (fun j hj => Real.rpow_nonneg (hP j hj) _)
  have hpowH : ∀ j ∈ s, ((H j)^(1/3:ℝ))^(3:ℝ)=H j := by
    intro j hj
    rw [← Real.rpow_mul (hH j hj)]
    norm_num
  have hpowP : ∀ j ∈ s, ((P j)^(2/3:ℝ))^(3/2:ℝ)=P j := by
    intro j hj
    rw [← Real.rpow_mul (hP j hj)]
    norm_num
  simp_rw [Finset.sum_congr rfl hpowH,Finset.sum_congr rfl hpowP] at hh
  norm_num at hh ⊢
  exact hh

theorem epoch_sqrt_sum {ι : Type*} (s : Finset ι) (H P : ι → ℝ)
    (hH : ∀ j ∈ s, 0 ≤ H j) (hP : ∀ j ∈ s, 0 ≤ P j) :
    (∑ j ∈ s,Real.sqrt (H j*(1+P j))) ≤
      Real.sqrt ((∑ j ∈ s,H j)*(s.card+∑ j ∈ s,P j)) := by
  have hh := Real.inner_le_Lp_mul_Lq_of_nonneg s (f := fun j => Real.sqrt (H j))
    (g := fun j => Real.sqrt (1+P j)) Real.HolderConjugate.two_two
    (fun j _ => Real.sqrt_nonneg _) (fun j _ => Real.sqrt_nonneg _)
  have hsH : ∀ j ∈ s,(Real.sqrt (H j))^(2:ℝ)=H j := by
    intro j hj
    rw [Real.rpow_two,Real.sq_sqrt (hH j hj)]
  have hsP : ∀ j ∈ s,(Real.sqrt (1+P j))^(2:ℝ)=1+P j := by
    intro j hj
    rw [Real.rpow_two,Real.sq_sqrt (by linarith [hP j hj])]
  simp_rw [Finset.sum_congr rfl hsH,Finset.sum_congr rfl hsP] at hh
  have hleft : (∑ j ∈ s,Real.sqrt (H j)*Real.sqrt (1+P j))=
      ∑ j ∈ s,Real.sqrt (H j*(1+P j)) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Real.sqrt_mul (hH j hj)]
  rw [hleft] at hh
  rw [Real.sqrt_mul (Finset.sum_nonneg hH)]
  simpa [Real.sqrt_eq_rpow,Finset.sum_add_distrib] using hh

/-- The scale is clipped separately in each epoch. The extra smoothing
cost is summable; no shared feasible scale is assumed. -/
theorem epoch_clipped_smoothing (H D τ : ℝ) (hH : 0 < H) (hD : 0 ≤ D) (hτ : 0 ≤ τ) :
    H*(max τ (D/H))^2 ≤ H*τ^2+D^2/H := by
  rcases le_total τ (D/H) with h | h
  · rw [max_eq_right h]
    have he : H*(D/H)^2=D^2/H := by field_simp <;> ring
    rw [he]
    linarith [mul_nonneg hH.le (sq_nonneg τ)]
  · rw [max_eq_left h]
    have : 0 ≤ D^2/H := by positivity
    linarith

end Paper254
#print axioms Paper254.epoch_curved_sum
#print axioms Paper254.epoch_sqrt_sum
