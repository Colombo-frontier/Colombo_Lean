import Smoothness2601.SineGeometry
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! Actual all-order derivatives of a vector sine/cosine wave. The global
derivative bound is uniform in the derivative order and in the vector space. -/
noncomputable section
open scoped ContDiff
namespace Smoothness2601.SineGeometry
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def wave (h : ℝ) (u v : E) (y : ℝ) : E := Real.sin (y/h) • u+Real.cos (y/h) • v

def waveJet (h : ℝ) : ℕ → E → E → ℝ → E
  | 0,u,v,y => wave h u v y
  | n+1,u,v,y => h⁻¹ • waveJet h n (-v) u y

theorem wave_hasDerivAt (h : ℝ) (u v : E) (y : ℝ) :
    HasDerivAt (wave h u v) (waveJet h 1 u v y) y := by
  have hs := (((hasDerivAt_id y).div_const h).sin.smul_const u).add
    (((hasDerivAt_id y).div_const h).cos.smul_const v)
  convert hs using 1
  simp only [waveJet,wave,smul_add,smul_neg,smul_smul,div_eq_mul_inv,id_eq]
  module

theorem waveJet_hasDerivAt (h : ℝ) (n : ℕ) (u v : E) (y : ℝ) :
    HasDerivAt (waveJet h n u v) (waveJet h (n+1) u v y) y := by
  induction n generalizing u v with
  | zero => exact wave_hasDerivAt h u v y
  | succ n ih => exact (ih (-v) u).const_smul h⁻¹

theorem wave_iteratedDeriv (h : ℝ) (n : ℕ) (u v : E) :
    iteratedDeriv n (wave h u v) = waveJet h n u v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    exact funext fun y => (waveJet_hasDerivAt h n u v y).deriv

theorem wave_contDiff (h : ℝ) (u v : E) : ContDiff ℝ ∞ (wave h u v) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro n _
  rw [wave_iteratedDeriv]
  exact fun y => (waveJet_hasDerivAt h n u v y).differentiableAt

theorem wave_norm_bound (h : ℝ) (u v : E) (y : ℝ) : ‖wave h u v y‖ ≤ ‖u‖+‖v‖ := by
  apply (norm_add_le _ _).trans
  simp only [norm_smul,Real.norm_eq_abs]
  exact add_le_add ((mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _) (norm_nonneg _)).trans_eq (one_mul _))
    ((mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (norm_nonneg _)).trans_eq (one_mul _))

theorem waveJet_norm_bound (h : ℝ) (n : ℕ) (u v : E) (y : ℝ) :
    ‖waveJet h n u v y‖ ≤ |h⁻¹|^n*(‖u‖+‖v‖) := by
  induction n generalizing u v with
  | zero => simpa using wave_norm_bound h u v y
  | succ n ih =>
    rw [waveJet,norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (ih (-v) u) (abs_nonneg _)).trans_eq (by
      rw [norm_neg,pow_succ]
      ring)

def affineWave (h : ℝ) (b u v : E) (y : ℝ) : E := y • b+wave h u v y

def affineWaveJet (h : ℝ) (b u v : E) : ℕ → ℝ → E
  | 0,y => affineWave h b u v y
  | 1,y => b+waveJet h 1 u v y
  | n+2,y => waveJet h (n+2) u v y

theorem affineWaveJet_hasDerivAt (h : ℝ) (b u v : E) (n : ℕ) (y : ℝ) :
    HasDerivAt (affineWaveJet h b u v n) (affineWaveJet h b u v (n+1) y) y := by
  rcases n with _ | _ | n
  · simpa only [affineWaveJet,affineWave,one_smul] using
      ((hasDerivAt_id y).smul_const b).add (wave_hasDerivAt h u v y)
  · exact (waveJet_hasDerivAt h 1 u v y).const_add b
  · exact waveJet_hasDerivAt h (n+2) u v y

theorem affineWave_iteratedDeriv (h : ℝ) (b u v : E) (n : ℕ) :
    iteratedDeriv n (affineWave h b u v) = affineWaveJet h b u v n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    exact funext fun y => (affineWaveJet_hasDerivAt h b u v n y).deriv

theorem affineWave_contDiff (h : ℝ) (b u v : E) : ContDiff ℝ ∞ (affineWave h b u v) :=
  (contDiff_id.smul contDiff_const).add (wave_contDiff h u v)

theorem affineWave_iteratedFDeriv_norm (h : ℝ) (b u v : E) (n : ℕ) (y : ℝ) :
    ‖iteratedFDeriv ℝ (n+2) (affineWave h b u v) y‖ ≤ |h⁻¹|^(n+2)*(‖u‖+‖v‖) := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,affineWave_iteratedDeriv]
  exact waveJet_norm_bound h (n+2) u v y

theorem affineWave_iteratedFDeriv_lipschitz (h : ℝ) (b u v : E) (n : ℕ) (y z : ℝ) :
    ‖iteratedFDeriv ℝ (n+2) (affineWave h b u v) y-
      iteratedFDeriv ℝ (n+2) (affineWave h b u v) z‖ ≤ |h⁻¹|^(n+3)*(‖u‖+‖v‖)*|y-z| := by
  rw [iteratedFDeriv_eq_equiv_comp]
  simp only [Function.comp_apply,← map_sub,LinearIsometryEquiv.norm_map,affineWave_iteratedDeriv]
  exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (waveJet_hasDerivAt h (n+2) u v t).hasDerivWithinAt)
    (fun t _ => waveJet_norm_bound h (n+3) u v t) convex_univ (Set.mem_univ z) (Set.mem_univ y)

end Smoothness2601.SineGeometry
