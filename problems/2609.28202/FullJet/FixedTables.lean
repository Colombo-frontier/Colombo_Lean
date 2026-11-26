import FullJet.ScaledChain
import FullJet.RareLowerBound
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Finset.Powerset

open scoped BigOperators InnerProductSpace

namespace FullJet

/-- A fixed column is specified by exactly `k` positive positions. -/
abbrev FixedColumn (n k : ℕ) := {S : Finset (Fin n) // S.card = k}

theorem fixedColumn_nonempty {n k : ℕ} (hk : k ≤ n) : Nonempty (FixedColumn n k) := by
  obtain ⟨S, hS, hcard⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin n))) (by simpa using hk)
  exact ⟨⟨S, hcard⟩⟩

def columnSign {n : ℕ} (S : Finset (Fin n)) (i : Fin n) : ℝ := if i ∈ S then 1 else -1

theorem columnSign_sq {n : ℕ} (S : Finset (Fin n)) (i : Fin n) : columnSign S i ^ 2 = 1 := by
  unfold columnSign
  split_ifs <;> norm_num

theorem sum_columnSign {n : ℕ} (S : Finset (Fin n)) :
    ∑ i, columnSign S i = 2 * (S.card : ℝ) - n := by
  have heq (i : Fin n) : columnSign S i = 2 * (if i ∈ S then (1 : ℝ) else 0) - 1 := by
    unfold columnSign
    split_ifs <;> norm_num
  simp_rw [heq]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp

/-- Normalize a real sign vector in the genuine Euclidean norm. -/
noncomputable def normalizedVector {D : ℕ} (v : Fin D → ℝ) : EuclideanSpace ℝ (Fin D) :=
  (WithLp.equiv 2 (Fin D → ℝ)).symm (fun l => v l / Real.sqrt D)

theorem normalizedVector_apply {D : ℕ} (v : Fin D → ℝ) (l : Fin D) :
    normalizedVector v l = v l / Real.sqrt D := rfl

theorem normalizedVector_norm {D : ℕ} (hD : 0 < D) (v : Fin D → ℝ)
    (hv : ∀ l, v l ^ 2 = 1) : ‖normalizedVector v‖ = 1 := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hn : ‖normalizedVector v‖ ^ 2 = 1 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [normalizedVector_apply, Real.norm_eq_abs, sq_abs, div_pow, hv,
      Real.sq_sqrt (Nat.cast_nonneg D), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
  nlinarith [norm_nonneg (normalizedVector v)]

/-- Independent hidden signs and fixed column encodings for one stage. -/
abbrev FixedTableSample (n D k : ℕ) := (Fin D → Bool) × (Fin D → FixedColumn n k)

noncomputable def fixedTableLaw (n D k : ℕ) (hk : k ≤ n) : PMF (FixedTableSample n D k) := by
  letI := fixedColumn_nonempty hk
  exact PMF.uniformOfFintype _

theorem fixedTableLaw_apply (n D k : ℕ) (hk : k ≤ n) (ω : FixedTableSample n D k) :
    fixedTableLaw n D k hk ω = (Fintype.card (FixedTableSample n D k) : ENNReal)⁻¹ := by
  letI := fixedColumn_nonempty hk
  unfold fixedTableLaw
  exact PMF.uniformOfFintype_apply ω

noncomputable def sampledDirection {n D k : ℕ} (ω : FixedTableSample n D k) : EuclideanSpace ℝ (Fin D) :=
  normalizedVector (fun l => rareSign (ω.1 l))

noncomputable def sampledRow {n D k : ℕ} (ω : FixedTableSample n D k) (i : Fin n) : EuclideanSpace ℝ (Fin D) :=
  normalizedVector (fun l => rareSign (ω.1 l) * columnSign (ω.2 l).val i)

theorem sampledDirection_norm {n D k : ℕ} (hD : 0 < D) (ω : FixedTableSample n D k) :
    ‖sampledDirection ω‖ = 1 := normalizedVector_norm hD _ (fun l => rareSign_sq _)

theorem sampledRow_norm {n D k : ℕ} (hD : 0 < D) (ω : FixedTableSample n D k) (i : Fin n) :
    ‖sampledRow ω i‖ = 1 := by
  apply normalizedVector_norm hD
  intro l
  rw [mul_pow, rareSign_sq, columnSign_sq, one_mul]

theorem sampledRow_sum {n D k m : ℕ} (hbalance : 2 * k = n + m)
    (ω : FixedTableSample n D k) :
    ∑ i, sampledRow ω i = (m : ℝ) • sampledDirection ω := by
  have hbal : 2 * (k : ℝ) - n = m := by
    have h : 2 * (k : ℝ) = n + m := by exact_mod_cast hbalance
    linarith
  ext l
  change (PiLp.proj 2 (fun _ : Fin D => ℝ) l : EuclideanSpace ℝ (Fin D) →L[ℝ] ℝ)
    (∑ i, sampledRow ω i) = _
  rw [map_sum]
  simp only [PiLp.smul_apply]
  change (∑ i, rareSign (ω.1 l) * columnSign (ω.2 l).val i / Real.sqrt D) =
    (m : ℝ) * (rareSign (ω.1 l) / Real.sqrt D)
  rw [← Finset.sum_div, ← Finset.mul_sum, sum_columnSign, (ω.2 l).property, hbal]
  ring

theorem sampledRow_table_average {n D k m : ℕ} (hn : 0 < n) (hbalance : 2 * k = n + m)
    (ω : FixedTableSample n D k) :
    ∑ i, sampledRow ω i = ((n : ℝ) * ((m : ℝ) / n)) • sampledDirection ω := by
  rw [sampledRow_sum hbalance]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  congr 1
  field_simp

/-- Every sample of the finite table law gives a valid hard-instance construction. -/
theorem sampledChain_admissible {n D k m T p : ℕ} (hn : 0 < n) (hD : 0 < D)
    (hm : 0 < m) (hmn : m ≤ n) (hbalance : 2 * k = n + m) (hp : 2 ≤ p)
    (ω : Fin (T + 1) → FixedTableSample n D k) (α β Δ L : ℝ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hgap : α * (2 * (T + 1 : ℕ)) ≤ Δ)
    (hsmooth : α * β ^ (p + 1) * (chainDerivativeBound (p + 1) / ((m : ℝ) / n)) ≤ L) :
    Admissible p n Δ L (fun i => scaledComponentChain
      (fun j => sampledDirection (ω j)) (fun j => sampledRow (ω j) i)
      ((m : ℝ) / n) (33 / 16) α β) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  exact scaledChain_admissible hn hp _ _
    (fun j => (sampledDirection_norm hD (ω j)).le)
    (fun i j => (sampledRow_norm hD (ω j) i).le)
    _ _ _ _ _ _ (div_pos hm' hn')
    ((div_le_one hn').mpr (by exact_mod_cast hmn)) (by norm_num) hα hβ
    (fun j => sampledRow_table_average hn hbalance (ω j)) hgap hsmooth

end FullJet
