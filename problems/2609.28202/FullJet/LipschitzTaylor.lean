import FullJet.TaylorModel
import Mathlib.Analysis.Calculus.Taylor

open Set
open scoped BigOperators Topology ContDiff

namespace FullJet

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Differentiating the Taylor polynomial with respect to its expansion center. -/
theorem taylor_center_hasDerivAt {f : ℝ → F} {n : ℕ}
    (hf : ContDiff ℝ (n + 1) f) (t x : ℝ) :
    HasDerivAt (fun y => taylorWithinEval f n univ y x)
      (((n.factorial : ℝ)⁻¹ * (x - t) ^ n) • iteratedDeriv (n + 1) f t) t := by
  have hd : Differentiable ℝ (iteratedDeriv n f) :=
    (contDiff_nat_iff_iteratedDeriv.mp hf).2 n (Nat.lt_succ_self n)
  have h := hasDerivWithinAt_taylorWithinEval (s := univ) (s' := univ)
    (x := x) (y := t) uniqueDiffOn_univ (by simp) (mem_univ t) (Subset.refl _)
    hf.of_succ.contDiffOn (by simpa only [iteratedDerivWithin_univ] using (hd t).differentiableWithinAt)
  simpa only [iteratedDerivWithin_univ] using h.hasDerivAt (by simp)

/-- A Taylor remainder estimate requiring only oscillation of the highest
continuous derivative, and no derivative of the next order. -/
theorem taylor_unit_remainder_of_derivative_oscillation {f : ℝ → F} {n : ℕ}
    (hf : ContDiff ℝ (n + 1) f) (C : ℝ)
    (hC : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖iteratedDeriv (n + 1) f t - iteratedDeriv (n + 1) f 0‖ ≤ C) :
    ‖f 1 - taylorWithinEval f (n + 1) univ 0 1‖ ≤ C / (n.factorial : ℝ) := by
  let g : ℝ → F := fun t => taylorWithinEval f n univ t 1 +
    ((((n + 1 : ℝ) * n.factorial)⁻¹ * (1 - t) ^ (n + 1)) • iteratedDeriv (n + 1) f 0)
  have hg (t : ℝ) : HasDerivAt g
      (((n.factorial : ℝ)⁻¹ * (1 - t) ^ n) •
        (iteratedDeriv (n + 1) f t - iteratedDeriv (n + 1) f 0)) t := by
    have hc : HasDerivAt (fun y : ℝ => ((n + 1 : ℝ) * n.factorial)⁻¹ * (1 - y) ^ (n + 1))
        (-((n.factorial : ℝ)⁻¹ * (1 - t) ^ n)) t := by
      convert (monomial_has_deriv_aux t 1 n).const_mul (((n + 1 : ℝ) * n.factorial)⁻¹) using 1
      field_simp
      ring
    convert (taylor_center_hasDerivAt hf t 1).add (hc.smul_const (iteratedDeriv (n + 1) f 0)) using 1
    simp only [smul_sub, neg_smul, sub_eq_add_neg, smul_add, smul_neg]
  have hnonneg : 0 ≤ C := by simpa using hC 0 (by norm_num)
  have hb (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) :
      ‖((n.factorial : ℝ)⁻¹ * (1 - t) ^ n) •
        (iteratedDeriv (n + 1) f t - iteratedDeriv (n + 1) f 0)‖ ≤ C / (n.factorial : ℝ) := by
    have hp : 0 ≤ 1 - t := by linarith [ht.2]
    rw [norm_smul, Real.norm_of_nonneg (mul_nonneg (by positivity) (pow_nonneg hp _))]
    calc
      _ ≤ (n.factorial : ℝ)⁻¹ * 1 * C := by
        gcongr
        · exact pow_le_one₀ hp (by linarith [ht.1])
        · exact hC t ⟨ht.1, ht.2.le⟩
      _ = _ := by ring
  have hm := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t _ => (hg t).hasDerivWithinAt) hb
  have hzero : g 0 = taylorWithinEval f (n + 1) univ 0 1 := by
    simp only [g, taylorWithinEval_succ, iteratedDerivWithin_univ, sub_zero]
  have hone : g 1 = f 1 := by simp [g]
  rwa [hzero, hone] at hm

end FullJet
