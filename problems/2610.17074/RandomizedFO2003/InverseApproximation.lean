import RandomizedFO2003.MarkovInterval
import RandomizedFO2003.SpectralDesign
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace RandomizedFO2003

open Polynomial Set

theorem inverse_approximation_unit (m : ℕ) (hm : 1 ≤ m) (L : ℝ)
    (hL : 2 ≤ L) (hscale : 256 * (m : ℝ) ^ 2 ≤ L)
    (p : Polynomial ℝ) (hp : p.natDegree < m) :
    ∃ x ∈ Icc (1 : ℝ) L, (1 / 16 : ℝ) ≤ |x⁻¹ - p.eval x| := by
  by_contra! hsmall
  have hb : ∀ x ∈ Icc (1 : ℝ) L, |p.eval x| ≤ (17 / 16 : ℝ) := by
    intro x hx
    have hxpos : 0 < x := by linarith [hx.1]
    have hinv : x⁻¹ ≤ 1 := by
      simpa [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hx.1
    have herr := hsmall x hx
    calc
      |p.eval x| = |x⁻¹ - (x⁻¹ - p.eval x)| := by congr 1; ring
      _ ≤ |x⁻¹| + |x⁻¹ - p.eval x| := abs_sub _ _
      _ ≤ 17 / 16 := by rw [abs_of_pos (inv_pos.mpr hxpos)]; linarith
  have hfirst := hsmall 1 (by constructor <;> linarith)
  have hsecond := hsmall 2 (by constructor <;> linarith)
  norm_num at hfirst hsecond
  have hp1 : 15 / 16 < p.eval 1 := by linarith [(abs_lt.mp hfirst).2]
  have hp2 : p.eval 2 < 9 / 16 := by linarith [(abs_lt.mp hsecond).1]
  obtain ⟨c, hc, hder⟩ := exists_hasDerivAt_eq_slope
    (fun x => p.eval x) (fun x => p.derivative.eval x) (by norm_num : (1 : ℝ) < 2)
    p.continuousOn (fun x _ => p.hasDerivAt x)
  norm_num at hder
  have hdneg : p.derivative.eval c < -(3 / 8 : ℝ) := by linarith
  have hdabs : (3 / 8 : ℝ) < |p.derivative.eval c| := by linarith [neg_le_abs (p.derivative.eval c)]
  have hmark := polynomial_markov_interval m (by omega) p hp.le 1 L (17 / 16)
    (by linarith) (by norm_num) hb c ⟨hc.1.le, hc.2.le.trans hL⟩
  have hmul := (le_div_iff₀ (by linarith : 0 < L - 1)).mp hmark
  nlinarith [mul_pos (sub_pos.mpr hdabs) (show 0 < L - 1 by linarith)]

/-- Lemma markov with explicit numerical constants. Squared regime form avoids
introducing a square root into downstream design construction. -/
theorem inverse_approximation_lower_bound (m : ℕ) (hm : 1 ≤ m) (γ L : ℝ)
    (hγ : 0 < γ) (hL : 2 * γ ≤ L) (hscale : 256 * γ * (m : ℝ) ^ 2 ≤ L)
    (p : Polynomial ℝ) (hp : p.natDegree < m) :
    ∃ x ∈ Icc γ L, 1 / (16 * γ) ≤ |x⁻¹ - p.eval x| := by
  let q : Polynomial ℝ := C γ * p.comp (C γ * X)
  have hqdeg : q.natDegree < m := by
    calc
      q.natDegree ≤ (p.comp (C γ * X)).natDegree := Polynomial.natDegree_C_mul_le _ _
      _ ≤ p.natDegree * (C γ * X).natDegree := Polynomial.natDegree_comp_le
      _ ≤ p.natDegree * 1 := Nat.mul_le_mul_left _ ((Polynomial.natDegree_C_mul_le _ _).trans (by simp))
      _ < m := by simpa using hp
  obtain ⟨t, ht, herr⟩ := inverse_approximation_unit m hm (L / γ)
    ((le_div_iff₀ hγ).mpr hL)
    ((le_div_iff₀ hγ).mpr (by nlinarith [hscale])) q hqdeg
  refine ⟨γ * t, ⟨?_, ?_⟩, ?_⟩
  · nlinarith [ht.1]
  · have h := (le_div_iff₀ hγ).mp ht.2
    nlinarith
  · have heq : t⁻¹ - q.eval t = γ * ((γ * t)⁻¹ - p.eval (γ * t)) := by
      simp only [q, eval_mul, eval_C, eval_comp, eval_X]
      rw [mul_inv_rev, mul_sub]
      congr 1
      calc
        t⁻¹ = t⁻¹ * (γ * γ⁻¹) := by rw [mul_inv_cancel₀ hγ.ne', mul_one]
        _ = γ * (t⁻¹ * γ⁻¹) := by ring
    rw [heq, abs_mul, abs_of_pos hγ] at herr
    apply (div_le_iff₀ (by positivity : 0 < 16 * γ)).mpr
    nlinarith

/-- The original square-root regime, with c₀=1/16 and c₁=1/16. -/
theorem inverse_approximation_sqrt_regime (m : ℕ) (hm : 1 ≤ m) (γ L : ℝ)
    (hγ : 0 < γ) (hL : 2 * γ ≤ L)
    (hregime : (m : ℝ) ≤ (1 / 16 : ℝ) * Real.sqrt (L / γ))
    (p : Polynomial ℝ) (hp : p.natDegree < m) :
    ∃ x ∈ Icc γ L, 1 / (16 * γ) ≤ |x⁻¹ - p.eval x| := by
  have hratio : 0 ≤ L / γ := div_nonneg (by linarith) hγ.le
  have hsq := Real.sq_sqrt hratio
  have hn : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hs : 256 * (m : ℝ) ^ 2 ≤ L / γ := by
    nlinarith [Real.sqrt_nonneg (L / γ)]
  have hmul := (le_div_iff₀ hγ).mp hs
  exact inverse_approximation_lower_bound m hm γ L hγ hL (by nlinarith) p hp

/-- A finite spectral design and nonzero orthogonal residual in the paper's
regime, now with no approximation lower bound supplied as a hypothesis. -/
theorem finite_spectral_design_sqrt_regime (m : ℕ) (hm : 1 ≤ m) (γ L : ℝ)
    (hγ : 0 < γ) (hL : 2 * γ ≤ L)
    (hregime : (m : ℝ) ≤ (1 / 16 : ℝ) * Real.sqrt (L / γ)) :
    Nonempty (FiniteSpectralDesign m γ L (1 / (16 * γ))) := by
  apply exists_finite_spectral_design m hm γ L (1 / (16 * γ)) hγ (by positivity)
  exact inverse_approximation_sqrt_regime m hm γ L hγ hL hregime

end RandomizedFO2003
