import Smoothness2601.DeferredPrefix
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Ring

/-! The deferred-prefix failure bound requires only T plus a logarithmic
residual dimension. The weaker verified tail changes an absolute constant. -/
noncomputable section
namespace Smoothness2601.DeferredPrefix
open MeasureTheory Bilevel EuclideanGaussian ProjectionPosterior
open scoped ENNReal

theorem failure_small (M T n : ℕ) (hM : 1 ≤ M) (hT : 1 ≤ T)
    {δ R : ℝ} (_hδ : 0 < δ) (_hR : 0 < R)
    (hn : Real.log (16*(M : ℝ)*T) ≤ (n : ℝ)*δ^2/(8*R^2)) :
    (M : ℝ≥0∞)*failurePerInspection T n δ R ≤ ENNReal.ofReal (1/8 : ℝ) := by
  have hMp : (0:ℝ) < M := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM)
  have hTp : (0:ℝ) < T := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hT)
  have hx : 0 < 16*(M : ℝ)*T := by positivity
  have he : Real.exp (-(n : ℝ)*(δ^2/R^2)/8) ≤ (16*(M : ℝ)*T)⁻¹ := by
    calc
      _ ≤ Real.exp (-Real.log (16*(M : ℝ)*T)) := by
        apply Real.exp_le_exp.mpr
        have hh : -(n : ℝ)*(δ^2/R^2)/8 = -((n : ℝ)*δ^2/(8*R^2)) := by ring
        rw [hh]
        linarith
      _ = _ := by rw [Real.exp_neg,Real.exp_log hx]
  have hb : (M : ℝ)*((T : ℝ)*(2*Real.exp (-(n : ℝ)*(δ^2/R^2)/8))) ≤ 1/8 := by
    have hh := mul_le_mul_of_nonneg_left he (show 0 ≤ 2*(M : ℝ)*T by positivity)
    have hid : 2*(M : ℝ)*T*(16*(M : ℝ)*T)⁻¹ = 1/8 := by field_simp; ring
    rw [hid] at hh
    nlinarith
  rw [failurePerInspection,← ENNReal.ofReal_natCast M,← ENNReal.ofReal_mul (Nat.cast_nonneg M)]
  exact ENNReal.ofReal_le_ofReal hb

def residualDimension (M T : ℕ) (δ R : ℝ) : ℕ :=
  ⌈(8*R^2/δ^2)*Real.log (16*(M : ℝ)*T)⌉₊

def ambientDimension (M T : ℕ) (δ R : ℝ) : ℕ := T+residualDimension M T δ R+1

theorem residualDimension_sufficient (M T : ℕ) {δ R : ℝ} (hδ : 0 < δ) (hR : 0 < R) :
    Real.log (16*(M : ℝ)*T) ≤ (residualDimension M T δ R : ℝ)*δ^2/(8*R^2) := by
  have hc := Nat.le_ceil ((8*R^2/δ^2)*Real.log (16*(M : ℝ)*T))
  change (8*R^2/δ^2)*Real.log (16*(M : ℝ)*T) ≤ (residualDimension M T δ R : ℝ) at hc
  apply (le_div_iff₀ (by positivity : 0 < 8*R^2)).mpr
  have hh := mul_le_mul_of_nonneg_right hc (sq_nonneg δ)
  have he : (8*R^2/δ^2)*Real.log (16*(M : ℝ)*T)*δ^2 = Real.log (16*(M : ℝ)*T)*(8*R^2) := by
    field_simp
    ring
  rw [he] at hh
  exact hh

theorem ambientDimension_upper (M T : ℕ) (hM : 1 ≤ M) (hT : 1 ≤ T)
    {δ R : ℝ} (hδ : 0 < δ) (hR : 0 < R) :
    (ambientDimension M T δ R : ℝ) <
      (T : ℝ)+2+(8*R^2/δ^2)*Real.log (16*(M : ℝ)*T) := by
  have hM' : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hT' : (1:ℝ) ≤ T := by exact_mod_cast hT
  have hl : 0 ≤ Real.log (16*(M : ℝ)*T) := Real.log_nonneg (by nlinarith)
  have hn : 0 ≤ (8*R^2/δ^2)*Real.log (16*(M : ℝ)*T) := by positivity
  have hc := Nat.ceil_lt_add_one hn
  unfold ambientDimension residualDimension
  push_cast
  linarith

theorem chosen_dimension_failure (M T : ℕ) (hM : 1 ≤ M) (hT : 1 ≤ T)
    {δ R : ℝ} (hδ : 0 < δ) (hR : 0 < R) (hδR : δ ≤ R)
    (P : Protocol (ambientDimension M T δ R) T 0 M T) (hP : Regular δ R P) :
    (HaarFrame.frameLaw (ambientDimension M T δ R) T (by unfold ambientDimension; omega))
      {U | bad δ P U} ≤ ENNReal.ofReal (1/8 : ℝ) := by
  apply (haar_failure_bound _ T M (residualDimension M T δ R)
    (by unfold ambientDimension; omega) P hδ hR hδR (by unfold ambientDimension; omega) hP).trans
  exact failure_small M T _ hM hT hδ hR (residualDimension_sufficient M T hδ hR)

end Smoothness2601.DeferredPrefix
