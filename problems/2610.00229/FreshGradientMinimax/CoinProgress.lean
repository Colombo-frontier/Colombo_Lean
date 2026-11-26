import FreshGradientMinimax.BernoulliCoins
import FreshGradientMinimax.IndependentMoments

/-! The exact reveal-count mean and the probability of exhausting the hidden
chain under the paper's horizon. The coin law is an actual finite iid product. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
open scoped BigOperators

def coinSuccessCount {n : ℕ} (w : Fin n → Bool) : ℕ := ∑ i, if w i then 1 else 0

theorem coinSuccessCount_snoc {n : ℕ} (w : Fin n → Bool) (c : Bool) :
    coinSuccessCount (Fin.snoc w c) = coinSuccessCount w + if c then 1 else 0 := by
  rw [coinSuccessCount, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, coinSuccessCount]

theorem coinSuccessCount_le {n : ℕ} (w : Fin n → Bool) : coinSuccessCount w ≤ n := by
  calc
    _ ≤ ∑ _i : Fin n, 1 := Finset.sum_le_sum (fun i _ => by split_ifs <;> omega)
    _ = n := by simp

theorem coinLaw_integral {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (f : Bool → ℝ) :
    (∫ c, f c ∂coinLaw p) = p * f true + (1 - p) * f false :=
  bernoulliKernel_integral hp hp1 (fun _ : Unit => true) (fun _ => false)
    measurable_const measurable_const () f

theorem coinSuccessCount_mean {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) :
    (∫ w, (coinSuccessCount w : ℝ) ∂coinWordLaw p n) = (n : ℝ) * p := by
  letI := coinLaw_probability hp hp1
  induction n with
  | zero => simp [coinWordLaw, coinSuccessCount]
  | succ n ih =>
    letI := coinWordLaw_probability hp hp1 n
    rw [coinWordLaw, integral_map (coinSnoc_measurable n).aemeasurable
      (measurable_of_countable (fun w : Fin (n + 1) → Bool => (coinSuccessCount w : ℝ))).aestronglyMeasurable]
    simp only [coinSnoc, coinSuccessCount_snoc, Nat.cast_add]
    calc
      _ = (∫ w, (coinSuccessCount w : ℝ) ∂coinWordLaw p n) +
          ∫ c, ((if c then 1 else 0 : ℕ) : ℝ) ∂coinLaw p :=
        independent_sum_mean Integrable.of_finite Integrable.of_finite
      _ = (n : ℝ) * p + p := by
        rw [ih, coinLaw_integral hp hp1]
        simp
      _ = _ := by push_cast; ring

theorem coinSuccessCount_tail {p B : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (hB : 0 < B) (n : ℕ) :
    (coinWordLaw p n).real {w | B ≤ (coinSuccessCount w : ℝ)} ≤ (n : ℝ) * p / B := by
  have h := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun w : Fin n → Bool => Nat.cast_nonneg (α := ℝ) (coinSuccessCount w)))
    (show Integrable (fun w : Fin n → Bool => (coinSuccessCount w : ℝ)) (coinWordLaw p n) from Integrable.of_finite) B
  rw [coinSuccessCount_mean hp hp1] at h
  exact (le_div_iff₀ hB).mpr (by nlinarith only [h])

theorem coinSuccessCount_exhaustion {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {N T : ℕ}
    (hT : 0 < T) (hN : (N : ℝ) ≤ (T : ℝ) / (12 * p)) :
    (coinWordLaw p N).real {w | T ≤ coinSuccessCount w} ≤ 1 / 12 := by
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have h := coinSuccessCount_tail hp.le hp1 hT' N
  have hs : {w : Fin N → Bool | (T : ℝ) ≤ (coinSuccessCount w : ℝ)} =
      {w : Fin N → Bool | T ≤ coinSuccessCount w} := by ext w; exact_mod_cast (Iff.rfl : T ≤ coinSuccessCount w ↔ T ≤ coinSuccessCount w)
  rw [hs] at h
  have hmul := (le_div_iff₀ (show 0 < 12 * p by positivity)).mp hN
  exact h.trans ((div_le_iff₀ hT').mpr (by nlinarith only [hmul]))

end FreshGradientMinimax
