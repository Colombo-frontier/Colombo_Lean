import NCConcave16991.DenseWeakSignColumn

/-! # Actual parity-compatible hidden-bit column distribution -/

noncomputable section

open scoped BigOperators

namespace NCConcave16991.DenseWeakHiding

set_option backward.isDefEq.respectTransparency false

def hiddenSign (θ : Fin 2) : ℝ := if θ = 0 then 1 else -1

def positiveCount (n m : ℕ) (θ : Fin 2) : ℕ :=
  if θ = 0 then (n + m) / 2 else (n - m) / 2

theorem positiveCount_le {n m : ℕ} (hm : m ≤ n) (θ : Fin 2) : positiveCount n m θ ≤ n := by
  unfold positiveCount
  split_ifs <;> omega

theorem positiveCount_encoding {n m : ℕ} (hm : m ≤ n) (hparity : m % 2 = n % 2)
    (θ : Fin 2) : 2 * (positiveCount n m θ : ℝ) - n = (m : ℝ) * hiddenSign θ := by
  unfold positiveCount hiddenSign
  split_ifs
  · have h : 2 * ((n + m) / 2) = n + m := by omega
    have hR : (2 : ℝ) * ((n + m) / 2 : ℕ) = (n : ℝ) + m := by exact_mod_cast h
    nlinarith only [hR]
  · have h : 2 * ((n - m) / 2) + m = n := by omega
    have hR : (2 : ℝ) * ((n - m) / 2 : ℕ) + m = n := by exact_mod_cast h
    nlinarith only [hR]

abbrev BiasColumn (n m : ℕ) (θ : Fin 2) := PositiveColumn (Fin n) (positiveCount n m θ)
abbrev EncodedColumn (n m : ℕ) := Σ θ : Fin 2, BiasColumn n m θ

def biasedColumnLaw (n m : ℕ) (hm : m ≤ n) : FiniteLaw (EncodedColumn n m) where
  mass := fun c ↦ (1 / 2 : ℝ) *
    (columnLaw (Fin n) (positiveCount n m c.1) (by simpa using positiveCount_le hm c.1)).mass c.2
  nonneg := fun c ↦ mul_nonneg (by norm_num)
    ((columnLaw (Fin n) (positiveCount n m c.1) (by simpa using positiveCount_le hm c.1)).nonneg c.2)
  sum_one := by
    have hs (θ : Fin 2) :
        (∑ A : BiasColumn n m θ,
          (columnLaw (Fin n) (positiveCount n m θ) (by simpa using positiveCount_le hm θ)).mass A) = 1 :=
      (columnLaw (Fin n) (positiveCount n m θ) (by simpa using positiveCount_le hm θ)).sum_one
    simp only [Fintype.sum_sigma, ← Finset.mul_sum, hs, mul_one, Fin.sum_univ_two]
    norm_num

theorem biasedColumn_label_mass {n m : ℕ} (hm : m ≤ n) (θ : Fin 2) :
    (∑ A : BiasColumn n m θ, (biasedColumnLaw n m hm).mass ⟨θ, A⟩) = 1 / 2 := by
  simp only [biasedColumnLaw, ← Finset.mul_sum]
  have hs := (columnLaw (Fin n) (positiveCount n m θ) (by simpa using positiveCount_le hm θ)).sum_one
  rw [hs]
  ring

theorem biasedColumn_sign_sum {n m : ℕ} (hm : m ≤ n) (hparity : m % 2 = n % 2)
    (c : EncodedColumn n m) :
    (∑ i : Fin n, columnSign c.2.val i) = (m : ℝ) * hiddenSign c.1 := by
  rw [columnSign_total]
  simpa only [Fintype.card_fin] using positiveCount_encoding hm hparity c.1

theorem hiddenSign_sq (θ : Fin 2) : hiddenSign θ ^ 2 = 1 := by
  unfold hiddenSign
  split_ifs <;> norm_num

theorem columnSign_sq {n m : ℕ} (c : EncodedColumn n m) (i : Fin n) :
    columnSign c.2.val i ^ 2 = 1 := by
  unfold columnSign
  split_ifs <;> norm_num

end NCConcave16991.DenseWeakHiding
