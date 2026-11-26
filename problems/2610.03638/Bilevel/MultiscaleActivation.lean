import Bilevel.IndependentDraws
import Bilevel.BernoulliOracle
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! The actual finite Bernoulli stream controls how many hidden columns can be revealed. -/
noncomputable section
open MeasureTheory
namespace Bilevel.MultiscaleActivation
open IndependentDraws

def count : (N : ℕ) → Draws Bool N → ℝ
  | 0, _ => 0
  | n+1, z => count n z.1 + if z.2 then 1 else 0

theorem count_bounds (N : ℕ) (z : Draws Bool N) : 0 ≤ count N z ∧ count N z ≤ N := by
  induction N with
  | zero => simp [count]
  | succ n ih =>
    have h := ih z.1
    cases hb : z.2 <;> simp only [count,hb,Bool.false_eq_true,if_false,if_true,Nat.cast_add,Nat.cast_one] <;>
      constructor <;> linarith

theorem count_measurable (N : ℕ) : Measurable (count N) := by
  induction N with
  | zero => exact measurable_const
  | succ n ih =>
    have hc : Measurable (fun b : Bool => if b then (1:ℝ) else 0) := measurable_of_countable _
    exact (ih.comp measurable_fst).add (hc.comp measurable_snd)

theorem count_integrable (N : ℕ) (p : ℝ) (hp1 : p ≤ 1) :
    Integrable (count N) (law (BernoulliOracle.law p hp1) N) := by
  apply (integrable_const (N : ℝ)).mono' (count_measurable N).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun z => by
    rw [Real.norm_eq_abs,abs_of_nonneg (count_bounds N z).1]
    exact (count_bounds N z).2)

theorem expected_count (N : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (∫ z, count N z ∂law (BernoulliOracle.law p hp1) N) = N*p := by
  induction N with
  | zero => simp [count]
  | succ n ih =>
    change (∫ z, count (n+1) z ∂(law (BernoulliOracle.law p hp1) n).prod (BernoulliOracle.law p hp1)) = _
    rw [integral_prod _ (count_integrable (n+1) p hp1)]
    have he : ∀ z : Draws Bool n, (∫ b, count (n+1) (z,b) ∂BernoulliOracle.law p hp1) = count n z+p := by
      intro z
      rw [BernoulliOracle.integral_law p hp0 hp1]
      simp only [count,Bool.false_eq_true,if_false,if_true,smul_eq_mul]
      ring
    simp_rw [he]
    rw [integral_add (count_integrable n p hp1) (integrable_const p),ih,integral_const]
    simp only [measureReal_univ_eq_one,one_smul,Nat.cast_add,Nat.cast_one]
    ring

theorem full_revelation_probability (N : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (T : ℝ) (hT : 0 < T) :
    (law (BernoulliOracle.law p hp1) N).real {z | T ≤ count N z} ≤ N*p/T := by
  have h := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun z => (count_bounds N z).1)) (count_integrable N p hp1) T
  rw [expected_count N p hp0 hp1] at h
  apply (le_div_iff₀ hT).mpr
  nlinarith

theorem revelation_sixteenth (N T : ℕ) (hT : 0 < T) (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hN : (N : ℝ) ≤ (T : ℝ)/(16*p)) :
    (law (BernoulliOracle.law p hp1) N).real {z | (T : ℝ) ≤ count N z} ≤ 1/16 := by
  apply (full_revelation_probability N p hp0.le hp1 T (Nat.cast_pos.mpr hT)).trans
  apply (div_le_iff₀ (Nat.cast_pos.mpr hT)).mpr
  have hh := (le_div_iff₀ (by positivity : 0 < 16*p)).mp hN
  nlinarith

end Bilevel.MultiscaleActivation
