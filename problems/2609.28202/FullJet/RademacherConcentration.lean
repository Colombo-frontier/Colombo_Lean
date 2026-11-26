import FullJet.ProductInformation
import FullJet.FixedTables
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

open scoped BigOperators InnerProductSpace

namespace FullJet

noncomputable def cubeWeight {D : ℕ} (theta : Fin D → Bool) : ℝ :=
  finiteProductWeight (fun _ : Fin D => bitWeight (1 / 2)) theta

theorem cubeWeight_nonneg {D : ℕ} (theta : Fin D → Bool) : 0 ≤ cubeWeight theta := by
  unfold cubeWeight finiteProductWeight
  apply Finset.prod_nonneg
  intro j hj
  exact (bitWeight_pos (1 / 2) (by norm_num) (by norm_num) (theta j)).le

theorem cubeWeight_sum (D : ℕ) : ∑ theta : Fin D → Bool, cubeWeight theta = 1 :=
  finiteProductWeight_sum _ (fun _ => bitWeight_sum _)

theorem cubeWeight_eq {D : ℕ} (theta : Fin D → Bool) : cubeWeight theta = (1 / 2 : ℝ) ^ D := by
  have h (b : Bool) : bitWeight (1 / 2) b = (1 / 2 : ℝ) := by cases b <;> norm_num [bitWeight]
  simp only [cubeWeight, finiteProductWeight, h, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Exact finite Rademacher moment-generating function. -/
theorem rademacher_mgf (D : ℕ) (v : Fin D → ℝ) (t : ℝ) :
    (∑ theta : Fin D → Bool, cubeWeight theta * Real.exp (t * ∑ j, v j * rareSign (theta j))) =
      ∏ j, Real.cosh (t * v j) := by
  have hbit (b : Bool) : bitWeight (1 / 2) b = (1 / 2 : ℝ) := by cases b <;> norm_num [bitWeight]
  have hpoint (theta : Fin D → Bool) :
      cubeWeight theta * Real.exp (t * ∑ j, v j * rareSign (theta j)) =
        ∏ j, (1 / 2 : ℝ) * Real.exp (t * (v j * rareSign (theta j))) := by
    simp only [cubeWeight, finiteProductWeight, hbit, Finset.mul_sum, Real.exp_sum]
    exact Finset.prod_mul_distrib.symm
  simp_rw [hpoint]
  have hsum := Finset.sum_prod_piFinset (ι := Fin D) (Finset.univ : Finset Bool)
    (fun j b => (1 / 2 : ℝ) * Real.exp (t * (v j * rareSign b)))
  simp only [Fintype.piFinset_univ] at hsum
  rw [hsum]
  apply Finset.prod_congr rfl
  intro j hj
  simp [rareSign, Real.cosh_eq]
  ring

theorem rademacher_mgf_le (D : ℕ) (v : Fin D → ℝ) (t : ℝ) :
    (∑ theta : Fin D → Bool, cubeWeight theta * Real.exp (t * ∑ j, v j * rareSign (theta j))) ≤
      Real.exp (t ^ 2 * (∑ j, v j ^ 2) / 2) := by
  rw [rademacher_mgf]
  calc
    ∏ j, Real.cosh (t * v j) ≤ ∏ j, Real.exp ((t * v j) ^ 2 / 2) :=
      Finset.prod_le_prod (fun j _ => (Real.cosh_pos _).le) (fun j _ => Real.cosh_le_exp_half_sq _)
    _ = Real.exp (t ^ 2 * (∑ j, v j ^ 2) / 2) := by
      rw [← Real.exp_sum]
      congr 1
      simp only [mul_pow, ← Finset.sum_div, ← Finset.mul_sum]

/-- Finite Chernoff bound; no measure-theoretic approximation is needed. -/
theorem finite_chernoff {α : Type*} [Fintype α] [DecidableEq α]
    (p X : α → ℝ) (hp : ∀ a, 0 ≤ p a) (t a : ℝ) (ht : 0 ≤ t) :
    (∑ x ∈ Finset.univ.filter (fun x => a ≤ X x), p x) ≤
      (∑ x, p x * Real.exp (t * X x)) / Real.exp (t * a) := by
  apply (le_div_iff₀ (Real.exp_pos _)).mpr
  rw [Finset.sum_mul]
  calc
    _ ≤ ∑ x ∈ Finset.univ.filter (fun x => a ≤ X x), p x * Real.exp (t * X x) := by
      apply Finset.sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hx).2 ht)) (hp x)
    _ ≤ ∑ x, p x * Real.exp (t * X x) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun x _ _ =>
        mul_nonneg (hp x) (Real.exp_pos _).le)

theorem rademacher_chernoff (D : ℕ) (v : Fin D → ℝ) (t a : ℝ) (ht : 0 ≤ t) :
    (∑ theta ∈ Finset.univ.filter (fun theta : Fin D → Bool => a ≤ ∑ j, v j * rareSign (theta j)),
      cubeWeight theta) ≤ Real.exp (t ^ 2 * (∑ j, v j ^ 2) / 2 - t * a) := by
  calc
    _ ≤ (∑ theta : Fin D → Bool, cubeWeight theta * Real.exp (t * ∑ j, v j * rareSign (theta j))) /
        Real.exp (t * a) := finite_chernoff _ _ cubeWeight_nonneg t a ht
    _ ≤ Real.exp (t ^ 2 * (∑ j, v j ^ 2) / 2) / Real.exp (t * a) :=
      div_le_div_of_nonneg_right (rademacher_mgf_le D v t) (Real.exp_pos _).le
    _ = _ := (Real.exp_sub _ _).symm

/-- Dimension-dependent alignment tail for a normalized hidden sign vector. -/
theorem rademacher_alignment_tail (D : ℕ) (v : Fin D → ℝ) (a : ℝ)
    (ha : 0 ≤ a) (hv : ∑ j, v j ^ 2 ≤ 1 / (D : ℝ)) (hD : 0 < D) :
    (∑ theta ∈ Finset.univ.filter (fun theta : Fin D → Bool => a ≤ ∑ j, v j * rareSign (theta j)),
      cubeWeight theta) ≤ Real.exp (-(a ^ 2 * D / 2)) := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  refine (rademacher_chernoff D v (a * D) a (mul_nonneg ha hD'.le)).trans ?_
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left hv (sq_nonneg (a * D))
  have hid : (a * (D : ℝ)) ^ 2 * (1 / D) = a ^ 2 * D := by field_simp; ring
  rw [hid] at h
  nlinarith

theorem finite_union_bound {α κ : Type*} [Fintype α] [Fintype κ]
    (p : α → ℝ) (hp : ∀ x, 0 ≤ p x) (A : κ → α → Prop)
    [∀ j, DecidablePred (A j)] :
    (∑ x ∈ Finset.univ.filter (fun x => ∃ j, A j x), p x) ≤
      ∑ j, ∑ x ∈ Finset.univ.filter (A j), p x := by
  classical
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x hx
  by_cases he : ∃ j, A j x
  · rw [if_pos he]
    obtain ⟨j, hj⟩ := he
    have h := Finset.single_le_sum
      (f := fun j => if A j x then p x else 0)
      (fun j _ => by dsimp only; split_ifs; exact hp x; exact le_rfl) (Finset.mem_univ j)
    simpa only [if_pos hj] using h
  · rw [if_neg he]
    exact Finset.sum_nonneg (fun j _ => by split_ifs; exact hp x; exact le_rfl)

/-- The reference probability covers alignment at any queried point, not just
alignment at the eventual output. -/
theorem rademacher_any_alignment_tail {κ : Type*} [Fintype κ]
    (D : ℕ) (v : κ → Fin D → ℝ) (a : ℝ) (ha : 0 ≤ a)
    (hv : ∀ l, ∑ j, v l j ^ 2 ≤ 1 / (D : ℝ)) (hD : 0 < D) :
    (∑ theta ∈ Finset.univ.filter (fun theta : Fin D → Bool =>
        ∃ l, a ≤ ∑ j, v l j * rareSign (theta j)), cubeWeight theta) ≤
      Fintype.card κ * Real.exp (-(a ^ 2 * D / 2)) := by
  classical
  calc
    _ ≤ ∑ l, ∑ theta ∈ Finset.univ.filter (fun theta : Fin D → Bool =>
        a ≤ ∑ j, v l j * rareSign (theta j)), cubeWeight theta :=
      finite_union_bound _ cubeWeight_nonneg _
    _ ≤ ∑ _ : κ, Real.exp (-(a ^ 2 * D / 2)) :=
      Finset.sum_le_sum (fun l _ => rademacher_alignment_tail D (v l) a ha (hv l) hD)
    _ = _ := by simp

theorem normalized_inner_eq {D : ℕ} (theta : Fin D → Bool) (w : EuclideanSpace ℝ (Fin D)) :
    ⟪normalizedVector (fun j => rareSign (theta j)), w⟫_ℝ =
      ∑ j, (w j / Real.sqrt D) * rareSign (theta j) := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [normalizedVector_apply, RCLike.inner_apply, conj_trivial]
  ring

theorem normalized_coeff_sq_sum {D : ℕ} (w : EuclideanSpace ℝ (Fin D)) (hw : ‖w‖ ≤ 1) :
    ∑ j, (w j / Real.sqrt D) ^ 2 ≤ 1 / (D : ℝ) := by
  have hnorm : ∑ j, w j ^ 2 = ‖w‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp
  simp_rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg D)]
  rw [← Finset.sum_div, hnorm]
  exact div_le_div_of_nonneg_right (by nlinarith [norm_nonneg w]) (Nat.cast_nonneg D)

/-- The bound is stated on the genuine Euclidean inner product appearing in
the chain construction, for any finite collection of query directions. -/
theorem euclidean_any_alignment_tail {κ : Type*} [Fintype κ]
    (D : ℕ) (w : κ → EuclideanSpace ℝ (Fin D)) (a : ℝ) (ha : 0 ≤ a)
    (hw : ∀ l, ‖w l‖ ≤ 1) (hD : 0 < D) :
    (∑ theta ∈ Finset.univ.filter (fun theta : Fin D → Bool =>
        ∃ l, a ≤ ⟪normalizedVector (fun j => rareSign (theta j)), w l⟫_ℝ), cubeWeight theta) ≤
      Fintype.card κ * Real.exp (-(a ^ 2 * D / 2)) := by
  simp_rw [normalized_inner_eq]
  exact rademacher_any_alignment_tail D _ a ha (fun l => normalized_coeff_sq_sum (w l) (hw l)) hD

end FullJet
