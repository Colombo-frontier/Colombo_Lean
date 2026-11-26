import FreshGradientMinimax.CoinCoupling
import FreshGradientMinimax.CoinProgress

/-! The number of successful coins strictly before each query. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators

def coinPrefixCount (c : ℕ → Bool) (t : ℕ) : ℕ := coinSuccessCount (fun i : Fin t => c i.val)

theorem coinPrefixCount_zero (c : ℕ → Bool) : coinPrefixCount c 0 = 0 := by
  simp [coinPrefixCount, coinSuccessCount]

theorem coinPrefixCount_succ (c : ℕ → Bool) (t : ℕ) :
    coinPrefixCount c (t + 1) = coinPrefixCount c t + if c t then 1 else 0 := by
  unfold coinPrefixCount coinSuccessCount
  rw [Fin.sum_univ_castSucc]
  rfl

theorem coinPrefixCount_monotone (c : ℕ → Bool) : Monotone (coinPrefixCount c) := by
  apply monotone_nat_of_le_succ
  intro t
  rw [coinPrefixCount_succ]
  exact Nat.le_add_right _ _

theorem coinPrefixCount_le (c : ℕ → Bool) (t : ℕ) : coinPrefixCount c t ≤ t :=
  coinSuccessCount_le _

theorem coinPrefixCount_word {N : ℕ} (w : Fin N → Bool) :
    coinPrefixCount (coinRead w) N = coinSuccessCount w := by
  simp only [coinPrefixCount, coinRead_fin]

theorem coinPrefixCount_word_le {N : ℕ} (w : Fin N → Bool) {t : ℕ} (ht : t ≤ N) :
    coinPrefixCount (coinRead w) t ≤ coinSuccessCount w := by
  simpa only [coinPrefixCount_word] using coinPrefixCount_monotone (coinRead w) ht

end FreshGradientMinimax
