import Bilevel.GenieProbability
import Bilevel.GenieEnergy

/-! Actual Haar-frame probability and simultaneous all-prefix energy control. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Bilevel.GenieProtocol
open EuclideanGaussian ProjectionPosterior ProjectionEnergy

theorem unsafe_probability (d T M R n : ℕ) (hT : T ≤ d)
    (P : Protocol d T M R) (b : ℝ) (hb : 0 < b) (hb2 : b ≤ 2)
    (hd : M+R+(n+1) ≤ d) (hcap : (R : ℝ)*((M : ℝ)*b) ≤ 1/2)
    (hP : Regular b P) (hV : Valid P ⊥) :
    (HaarFrame.frameLaw d T hT) {U | ¬ Safe (envelope ((M : ℝ)*b) R) P ⊥ ∅ U} ≤
      (M : ℝ≥0∞) * failurePerQuery T n b := by
  have hsub : {U : Frame d T | ¬ Safe (envelope ((M : ℝ)*b) R) P ⊥ ∅ U} ≤ᵐ[HaarFrame.frameLaw d T hT]
      {U | bad b P U} := by
    filter_upwards [ProjectionConcentration.haar_orthonormal_ae d T hT] with U hU
    intro hsafe
    by_contra hbad
    exact hsafe (initial_safe b hb.le (by linarith) P hV U hU hbad)
  exact (measure_mono_ae hsub).trans (haar_failure_bound d T M R n hT P b hb hb2 hd hP hV)

theorem envelope_twice (M R : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (hcap : (R : ℝ)*((M : ℝ)*b) ≤ 1/2) :
    envelope ((M : ℝ)*b) R ≤ 2*(M : ℝ)*b := by
  have h := envelope_le_twice ((M : ℝ)*b) R (mul_nonneg (Nat.cast_nonneg M) hb) hcap
  simpa only [mul_assoc] using h

def logarithmicIncrement (M T n : ℕ) (δ : ℝ) : ℝ :=
  8 * Real.log (4*(M : ℝ)*T/δ) / n

theorem logarithmic_failure_identity (M T n : ℕ) (hM : 0 < M) (hT : 0 < T)
    (hn : 0 < n) (δ : ℝ) (hδ : 0 < δ) :
    (M : ℝ) * ((T : ℝ)*(2*Real.exp (-(n : ℝ)*logarithmicIncrement M T n δ/8))) = δ/2 := by
  have hMn : (M : ℝ) ≠ 0 := (Nat.cast_pos.mpr hM).ne'
  have hTn : (T : ℝ) ≠ 0 := (Nat.cast_pos.mpr hT).ne'
  have hnn : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  have hx : 0 < 4*(M : ℝ)*T/δ := by positivity
  have he : -(n : ℝ)*logarithmicIncrement M T n δ/8 = -Real.log (4*(M : ℝ)*T/δ) := by
    unfold logarithmicIncrement
    field_simp
    ring
  rw [he, Real.exp_neg, Real.exp_log hx]
  field_simp
  ring

theorem logarithmic_increment_pos (M T n : ℕ) (hM : 0 < M) (hT : 0 < T)
    (hn : 0 < n) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    0 < logarithmicIncrement M T n δ := by
  have hm : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have ht : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hprod : 1 ≤ (M : ℝ)*T := by nlinarith
  have harg : 1 < 4*(M : ℝ)*T/δ := (lt_div_iff₀ hδ).mpr (by nlinarith)
  exact div_pos (mul_pos (by norm_num) (Real.log_pos harg)) (Nat.cast_pos.mpr hn)

end Bilevel.GenieProtocol
