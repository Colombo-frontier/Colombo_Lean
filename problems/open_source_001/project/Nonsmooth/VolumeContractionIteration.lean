import Nonsmooth.ProtasovVolumeCertificate
import Mathlib.Tactic

open scoped ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem finite_volume_fraction_to_contraction {a b : ℝ≥0∞} {c : ℝ}
    (hb : b < ∞) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (h : a + ENNReal.ofReal c * b ≤ b) : a ≤ ENNReal.ofReal (1 - c) * b := by
  have hab : a ≤ b := (le_add_of_nonneg_right (zero_le)).trans h
  have ha : a ≠ ∞ := (lt_of_le_of_lt hab hb).ne
  have hcb : ENNReal.ofReal c * b ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hb.ne
  have hsum : a + ENNReal.ofReal c * b ≠ ∞ := (lt_of_le_of_lt h hb).ne
  have hreal := (ENNReal.toReal_le_toReal hsum hb.ne).mpr h
  rw [ENNReal.toReal_add ha hcb, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc] at hreal
  apply (ENNReal.toReal_le_toReal ha (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hb.ne)).mp
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sub_nonneg.mpr hc1)]
  nlinarith only [hreal]

theorem volume_contraction_iterate (v : ℕ → ℝ≥0∞) (q : ℝ≥0∞) (N : ℕ)
    (hstep : ∀ n < N, v (n + 1) ≤ q * v n) : v N ≤ q ^ N * v 0 := by
  have haux (n : ℕ) (hn : n ≤ N) : v n ≤ q ^ n * v 0 := by
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 := hstep n (by omega)
      have h2 := mul_le_mul_left' (ih (by omega)) q
      calc
        v (n + 1) ≤ q * v n := h1
        _ ≤ q * (q ^ n * v 0) := h2
        _ = q ^ (n + 1) * v 0 := by rw [pow_succ]; ring
  exact haux N le_rfl

theorem volume_fraction_iterate (v : ℕ → ℝ≥0∞) {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hv0 : v 0 < ∞) (N : ℕ)
    (hstep : ∀ n < N, v (n + 1) + ENNReal.ofReal c * v n ≤ v n) :
    v N ≤ ENNReal.ofReal (1 - c) ^ N * v 0 := by
  have hfinite (n : ℕ) (hn : n ≤ N) : v n < ∞ := by
    induction n with
    | zero => exact hv0
    | succ n ih =>
      have hle : v (n + 1) ≤ v n :=
        (le_add_of_nonneg_right (zero_le)).trans (hstep n (by omega))
      exact lt_of_le_of_lt hle (ih (by omega))
  apply volume_contraction_iterate
  intro n hn
  exact finite_volume_fraction_to_contraction (hfinite n hn.le) hc hc1 (hstep n hn)

end
end Nonsmooth
