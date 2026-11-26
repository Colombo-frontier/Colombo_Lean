import FullJet.RademacherConcentration
import FullJet.InformationEvent

open scoped BigOperators InnerProductSpace

namespace FullJet

/-- The entropy event bound with an exponential reference probability, also
covering events with reference probability zero. -/
theorem finiteKL_event_of_exp_bound {α : Type*} [Fintype α] [DecidableEq α]
    (p q : α → ℝ) (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (hpsum : ∑ x, p x = 1) (hqsum : ∑ x, q x = 1)
    (hpq : ∀ x, p x ≠ 0 → q x ≠ 0) (A : Finset α) (B : ℝ) (hB : 0 < B)
    (hrare : ∑ x ∈ A, q x ≤ Real.exp (-B)) :
    ∑ x ∈ A, p x ≤ (finiteKL p q + Real.log 2) / B := by
  by_cases hz : ∑ x ∈ A, q x = 0
  · have hpz : ∑ x ∈ A, p x = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      by_contra hpx
      have hqx : 0 < q x := lt_of_le_of_ne (hq x) (Ne.symm (hpq x hpx))
      have hle := Finset.single_le_sum (fun y _ => hq y) hx
      rw [hz] at hle
      linarith
    rw [hpz]
    exact div_nonneg (add_nonneg (finiteKL_nonneg p q hp hq hpsum hqsum hpq)
      (Real.log_nonneg (by norm_num))) hB.le
  · have hqA : 0 < ∑ x ∈ A, q x :=
      lt_of_le_of_ne (Finset.sum_nonneg (fun x _ => hq x)) (Ne.symm hz)
    have hlog : B ≤ Real.log (1 / ∑ x ∈ A, q x) := by
      have h := Real.log_le_log hqA hrare
      rw [Real.log_exp] at h
      rw [one_div, Real.log_inv]
      linarith
    apply (le_div_iff₀ hB).mpr
    exact (mul_le_mul_of_nonneg_left hlog (Finset.sum_nonneg (fun x _ => hp x))).trans
      (finiteKL_event_bound p q hp hq hpsum hqsum hpq A hqA)

noncomputable def independentReference {D : ℕ} {Y : Type*} (r : Y → ℝ)
    (z : (Fin D → Bool) × Y) : ℝ := cubeWeight z.1 * r z.2

theorem independentReference_nonneg {D : ℕ} {Y : Type*} (r : Y → ℝ)
    (hr : ∀ y, 0 ≤ r y) (z : (Fin D → Bool) × Y) : 0 ≤ independentReference r z :=
  mul_nonneg (cubeWeight_nonneg _) (hr _)

theorem independentReference_sum (D : ℕ) {Y : Type*} [Fintype Y] (r : Y → ℝ)
    (hrsum : ∑ y, r y = 1) : ∑ z : (Fin D → Bool) × Y, independentReference r z = 1 := by
  unfold independentReference
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, hrsum, mul_one]
  exact cubeWeight_sum D

/-- Under the independent reference law, a query may be an arbitrary function
of the whole transcript; the bound covers any one of a finite list of queries. -/
theorem independentReference_alignment_tail (D : ℕ) {Y κ : Type*} [Fintype Y] [Fintype κ]
    (r : Y → ℝ) (hr : ∀ y, 0 ≤ r y) (hrsum : ∑ y, r y = 1)
    (w : Y → κ → EuclideanSpace ℝ (Fin D)) (hw : ∀ y l, ‖w y l‖ ≤ 1)
    (a : ℝ) (ha : 0 ≤ a) (hD : 0 < D) :
    (∑ z ∈ Finset.univ.filter (fun z : (Fin D → Bool) × Y =>
      ∃ l, a ≤ ⟪normalizedVector (fun j => rareSign (z.1 j)), w z.2 l⟫_ℝ), independentReference r z) ≤
      Fintype.card κ * Real.exp (-(a ^ 2 * D / 2)) := by
  classical
  have heq :
      (∑ z ∈ Finset.univ.filter (fun z : (Fin D → Bool) × Y =>
        ∃ l, a ≤ ⟪normalizedVector (fun j => rareSign (z.1 j)), w z.2 l⟫_ℝ), independentReference r z) =
      ∑ y, r y * (∑ theta ∈ Finset.univ.filter (fun theta : Fin D → Bool =>
        ∃ l, a ≤ ⟪normalizedVector (fun j => rareSign (theta j)), w y l⟫_ℝ), cubeWeight theta) := by
    simp only [Finset.sum_filter, independentReference]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y hy
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro theta ht
    split_ifs <;> ring
  rw [heq]
  calc
    _ ≤ ∑ y, r y * (Fintype.card κ * Real.exp (-(a ^ 2 * D / 2))) :=
      Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left
        (euclidean_any_alignment_tail D (w y) a ha (hw y) hD) (hr y))
    _ = _ := by rw [← Finset.sum_mul, hrsum, one_mul]

/-- Relative entropy transfers the independent alignment tail to an arbitrary
joint law of hidden signs and transcript. -/
theorem alignment_probability_from_information (D : ℕ) {Y κ : Type*} [Fintype Y] [Fintype κ]
    (p : ((Fin D → Bool) × Y) → ℝ) (r : Y → ℝ)
    (hp : ∀ z, 0 ≤ p z) (hpsum : ∑ z, p z = 1)
    (hr : ∀ y, 0 ≤ r y) (hrsum : ∑ y, r y = 1)
    (hpr : ∀ z, p z ≠ 0 → independentReference r z ≠ 0)
    (w : Y → κ → EuclideanSpace ℝ (Fin D)) (hw : ∀ y l, ‖w y l‖ ≤ 1)
    (a B : ℝ) (ha : 0 ≤ a) (hD : 0 < D) (hB : 0 < B)
    (hbudget : Fintype.card κ * Real.exp (-(a ^ 2 * D / 2)) ≤ Real.exp (-B)) :
    (∑ z ∈ Finset.univ.filter (fun z : (Fin D → Bool) × Y =>
      ∃ l, a ≤ ⟪normalizedVector (fun j => rareSign (z.1 j)), w z.2 l⟫_ℝ), p z) ≤
      (finiteKL p (independentReference r) + Real.log 2) / B := by
  classical
  apply finiteKL_event_of_exp_bound p (independentReference r) hp (independentReference_nonneg r hr)
    hpsum (independentReference_sum D r hrsum) hpr _ B hB
  exact (independentReference_alignment_tail D r hr hrsum w hw a ha hD).trans hbudget

end FullJet
