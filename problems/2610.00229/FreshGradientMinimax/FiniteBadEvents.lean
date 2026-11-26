import FreshGradientMinimax.FiniteResampling

/-! Finite probability bounds for hidden projections and label collisions.
Every average is over the full independent label list, without conditioning
on the absence of earlier failures or collisions. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators

def truthValue (P : Prop) : ℝ := @ite ℝ P (Classical.propDecidable P) 1 0

theorem truthValue_nonneg (P : Prop) : 0 ≤ truthValue P := by
  classical
  unfold truthValue
  split_ifs <;> norm_num

theorem truthValue_le_one (P : Prop) : truthValue P ≤ 1 := by
  classical
  unfold truthValue
  split_ifs <;> norm_num

theorem truthValue_or_le (P Q : Prop) : truthValue (P ∨ Q) ≤ truthValue P + truthValue Q := by
  classical
  by_cases hp : P <;> by_cases hq : Q <;> simp [truthValue, hp, hq]

theorem truthValue_mono {P Q : Prop} (h : P → Q) : truthValue P ≤ truthValue Q := by
  classical
  by_cases hp : P
  · simp [truthValue, hp, h hp]
  · rw [truthValue, if_neg hp]
    exact truthValue_nonneg Q

theorem truthValue_exists_le {I : Type*} [Fintype I] (P : I → Prop) :
    truthValue (∃ i, P i) ≤ ∑ i, truthValue (P i) := by
  classical
  by_cases h : ∃ i, P i
  · obtain ⟨i, hi⟩ := h
    have hs := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset I)) => truthValue_nonneg (P j))
      (Finset.mem_univ i)
    simpa only [truthValue, if_pos hi, if_pos (show ∃ i, P i from ⟨i, hi⟩)] using hs
  · simp only [truthValue, if_neg h]
    exact Finset.sum_nonneg (fun i _ => truthValue_nonneg (P i))

theorem truthValue_abs_square {a x : ℝ} (ha : 0 < a) :
    truthValue (a < |x|) ≤ x ^ 2 / a ^ 2 := by
  classical
  by_cases h : a < |x|
  · rw [truthValue, if_pos h]
    apply (le_div_iff₀ (sq_pos_of_pos ha)).mpr
    nlinarith [sq_abs x]
  · rw [truthValue, if_neg h]
    positivity

theorem expect_hidden_projection {m D : ℕ} [NeZero D]
    (q : (Fin m → Fin D) → Euclid D) (i : Fin m)
    (hind : ∀ z j, q (Function.update z i j) = q z)
    {B a : ℝ} (ha : 0 < a) (hq : ∀ z, ‖q z‖ ≤ B) :
    (𝔼 z, truthValue (a < |q z (z i)|)) ≤ B ^ 2 / ((D : ℝ) * a ^ 2) := by
  calc
    _ ≤ 𝔼 z, (q z (z i)) ^ 2 / a ^ 2 :=
      Finset.expect_le_expect (fun z _ => truthValue_abs_square ha)
    _ = (𝔼 z, (q z (z i)) ^ 2) / a ^ 2 :=
      (Finset.expect_div _ (fun z : Fin m → Fin D => (q z (z i)) ^ 2) (a ^ 2)).symm
    _ ≤ (B ^ 2 / D) / a ^ 2 := div_le_div_of_nonneg_right
      (expect_hidden_coordinate_square_le q i hind hq) (sq_nonneg a)
    _ = _ := by rw [div_div]

theorem expect_label_collision {m D : ℕ} [NeZero D] (i j : Fin m) (hij : i ≠ j) :
    (𝔼 z : Fin m → Fin D, truthValue (z i = z j)) = 1 / (D : ℝ) := by
  classical
  rw [expect_resample i]
  have hi (z : Fin m → Fin D) :
      (𝔼 k : Fin D, truthValue ((Function.update z i k) i = (Function.update z i k) j)) =
        1 / (D : ℝ) := by
    simp only [Function.update_self, Function.update_of_ne hij.symm]
    rw [Fintype.expect_eq_sum_div_card]
    simp only [truthValue, Fintype.card_fin]
    rw [Finset.sum_eq_single (z j)]
    · simp
    · intro k _ hk
      simp only [hk, if_false]
    · intro h
      exact False.elim (h (Finset.mem_univ _))
  simp_rw [hi]
  exact Fintype.expect_const _

theorem collision_indicator_le {m D : ℕ} (z : Fin m → Fin D) :
    truthValue (¬ Function.Injective z) ≤ ∑ i, ∑ j, truthValue (i ≠ j ∧ z i = z j) := by
  classical
  have h : ¬ Function.Injective z → ∃ i, ∃ j, i ≠ j ∧ z i = z j := by
    intro hz
    simp only [Function.Injective, not_forall] at hz
    obtain ⟨i, j, he, hne⟩ := hz
    exact ⟨i, j, hne, he⟩
  exact (truthValue_mono h).trans ((truthValue_exists_le _).trans
    (Finset.sum_le_sum (fun i _ => truthValue_exists_le _)))

theorem expect_collision_le {m D : ℕ} [NeZero D] :
    (𝔼 z : Fin m → Fin D, truthValue (¬ Function.Injective z)) ≤ (m : ℝ) ^ 2 / D := by
  classical
  have hp (i j : Fin m) :
      (𝔼 z : Fin m → Fin D, truthValue (i ≠ j ∧ z i = z j)) ≤ 1 / (D : ℝ) := by
    by_cases hij : i = j
    · simp only [hij, ne_eq, not_true_eq_false, false_and, truthValue, if_false, Finset.expect_const_zero]
      positivity
    · have he : (fun z : Fin m → Fin D => truthValue (i ≠ j ∧ z i = z j)) =
          (fun z : Fin m → Fin D => truthValue (z i = z j)) := by
        funext z
        simp [hij]
      rw [he]
      exact (expect_label_collision i j hij).le
  calc
    _ ≤ 𝔼 z : Fin m → Fin D, ∑ i, ∑ j, truthValue (i ≠ j ∧ z i = z j) :=
      Finset.expect_le_expect (fun z _ => collision_indicator_le z)
    _ = ∑ i : Fin m, ∑ j : Fin m, 𝔼 z : Fin m → Fin D, truthValue (i ≠ j ∧ z i = z j) := by
      simp only [Finset.expect_sum_comm]
    _ ≤ ∑ _ : Fin m, ∑ _ : Fin m, (1 / (D : ℝ)) :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hp i j))
    _ = _ := by simp; ring

end FreshGradientMinimax
