import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Log
import Audit254

namespace Paper254

def historyLifetime (i : ℕ) : ℕ := 2^(padicValNat 2 i+2)
def HistoryActive (t i : ℕ) : Prop := 1 ≤ i ∧ i ≤ t ∧ t-i ≤ historyLifetime i

theorem historyLifetime_ge_four (i : ℕ) : 4 ≤ historyLifetime i := by
  unfold historyLifetime
  have hh := Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : ℕ)) (show 2 ≤ padicValNat 2 i+2 by omega)
  exact hh

theorem historyActive_birth (t : ℕ) (ht : 1 ≤ t) : HistoryActive t t := by
  exact ⟨ht, le_rfl, by simp⟩

theorem historyActive_prefix {i t s : ℕ} (h : HistoryActive s i) (hi : i ≤ t) (ht : t ≤ s) :
    HistoryActive t i := ⟨h.1, hi, le_trans (Nat.sub_le_sub_right ht i) h.2.2⟩

theorem historyActive_no_return {i t s : ℕ} (hi : 1 ≤ i) (hit : i ≤ t)
    (h : ¬ HistoryActive t i) (ht : t ≤ s) : ¬ HistoryActive s i := by
  intro hs
  exact h (historyActive_prefix hs hit ht)

theorem historyLifetime_dvd_lower {i k : ℕ} (hi : 0 < i) (hk : 2^k ∣ i) :
    4*2^k ≤ historyLifetime i := by
  have hv : k ≤ padicValNat 2 i := (padicValNat_dvd_iff_le (p := 2) (ne_of_gt hi)).mp hk
  have hp := Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : ℕ)) (Nat.add_le_add_right hv 2)
  simpa [historyLifetime, pow_add, Nat.mul_comm] using hp

theorem streaming_history_cover (r s : ℕ) (hr : 1 ≤ r) (hrs : r ≤ s) :
    ∃ i, r ≤ i ∧ i ≤ (r+s)/2 ∧ HistoryActive s i := by
  by_cases hsmall : s-r < 2
  · refine ⟨r, le_rfl, by omega, hr, hrs, ?_⟩
    exact le_trans (by omega : s-r ≤ 4) (historyLifetime_ge_four r)
  let delta := s-r
  let k := Nat.log 2 (delta/2)
  let b := 2^k
  have hhalf : 0 < delta/2 := by dsimp [delta]; omega
  have hb : 0 < b := by dsimp [b]; positivity
  have hblo : b ≤ delta/2 := Nat.pow_log_le_self 2 (ne_of_gt hhalf)
  have hbhi : delta/2 < 2*b := by
    have hh := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) (delta/2)
    simpa [k, b, pow_succ, Nat.mul_comm] using hh
  let i := b*((r-1)/b+1)
  have hieq : i = b*((r-1)/b)+b := by dsimp [i]; ring
  have hmod := Nat.mod_lt (r-1) hb
  have hdiv := Nat.mod_add_div (r-1) b
  have hri : r ≤ i := by omega
  have hib : i ≤ r+b-1 := by omega
  have himid : i ≤ (r+s)/2 := by dsimp [delta] at hblo; omega
  have his : i ≤ s := by omega
  have hipos : 0 < i := by omega
  have hdi : 2^k ∣ i := ⟨(r-1)/b+1, rfl⟩
  have hlife := historyLifetime_dvd_lower hipos hdi
  refine ⟨i, hri, himid, by omega, his, ?_⟩
  have hdelta : delta < 4*b := by omega
  dsimp [delta] at hdelta
  exact le_trans (by omega : s-i ≤ 4*b) hlife

end Paper254
#print axioms Paper254.streaming_history_cover
