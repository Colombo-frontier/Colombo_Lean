import NoisyZO.HardPerturbation
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Unit-scale radial profile for the hard family

This file identifies the concrete hard objective with the exact rescaled
profile used in Appendix A of `2401.tex`.  In particular, the hidden Boolean
direction has norm one, and the perturbation is
`-a h^beta F_s (x / h)` with a dimension-free unit-scale profile `F_s`.
-/

open scoped BigOperators ContDiff Gradient InnerProductSpace

namespace NoisyZO

noncomputable section

/-- The normalized Boolean direction `s / sqrt d`. -/
def hypercubeDirection {d : ℕ} (s : Hypercube d) : Point d :=
  (Real.sqrt d)⁻¹ • signPoint (hypercubeSign s)

/-- The manuscript's unit-scale profile
`F_v(w) = inner v w * chi (‖w‖²)`, written in coordinates. -/
def normalizedRadialProfile {d : ℕ} (s : Hypercube d) (w : Point d) : ℝ :=
  (signedSum (hypercubeSign s) w / Real.sqrt d) *
    smoothCutoffProfile (‖w‖ ^ 2)

/-- The unit-scale profile is smooth to every finite order. -/
theorem normalizedRadialProfile_contDiff
    {d : ℕ} {n : ℕ∞} (s : Hypercube d) :
    ContDiff ℝ n (normalizedRadialProfile s) := by
  unfold normalizedRadialProfile
  have hlinear : ContDiff ℝ n (fun w : Point d ↦
      signedSum (hypercubeSign s) w) := by
    unfold signedSum
    fun_prop
  exact (hlinear.div_const _).mul
    (smoothCutoffProfile_contDiff.comp (contDiff_norm_sq ℝ))

/-- The unit-scale profile is `C∞`. -/
theorem normalizedRadialProfile_contDiff_infty
    {d : ℕ} (s : Hypercube d) :
    ContDiff ℝ ∞ (normalizedRadialProfile s) := by
  rw [contDiff_infty]
  intro n
  exact normalizedRadialProfile_contDiff s

/-- The unit profile vanishes outside the closed unit ball. -/
theorem normalizedRadialProfile_eq_zero_of_one_le_norm
    {d : ℕ} (s : Hypercube d) {w : Point d} (hw : 1 ≤ ‖w‖) :
    normalizedRadialProfile s w = 0 := by
  have hsq : 1 ≤ ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  unfold normalizedRadialProfile
  rw [smoothCutoffProfile_eq_zero_of_one_le hsq, mul_zero]

/-- The explicit unit-scale profile has compact support. -/
theorem normalizedRadialProfile_hasCompactSupport
    {d : ℕ} (s : Hypercube d) :
    HasCompactSupport (normalizedRadialProfile s) := by
  refine (isCompact_closedBall (0 : Point d) 1).of_isClosed_subset
    (isClosed_tsupport _) ?_
  apply closure_minimal
  · intro w hw
    simp only [Metric.mem_closedBall, dist_zero_right]
    by_contra hn
    have hnorm : 1 ≤ ‖w‖ := le_of_not_ge hn
    exact hw (normalizedRadialProfile_eq_zero_of_one_le_norm s hnorm)
  · exact Metric.isClosed_closedBall

theorem signedSum_smul {d : ℕ} (s : Fin d → ℝ) (r : ℝ) (x : Point d) :
    signedSum s (r • x) = r * signedSum s x := by
  classical
  unfold signedSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [PiLp.smul_apply]
  simp only [smul_eq_mul]
  ring

theorem normalizedRadialProfile_eq_inner {d : ℕ} (s : Hypercube d)
    (w : Point d) :
    normalizedRadialProfile s w =
      ⟪hypercubeDirection s, w⟫_ℝ * smoothCutoffProfile (‖w‖ ^ 2) := by
  rw [normalizedRadialProfile, hypercubeDirection, real_inner_smul_left,
    real_inner_signPoint]
  ring

/-- The normalized Boolean direction really has Euclidean norm one. -/
theorem norm_hypercubeDirection {d : ℕ} (hd : 0 < d) (s : Hypercube d) :
    ‖hypercubeDirection s‖ = 1 := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hsqrt : 0 < Real.sqrt d := Real.sqrt_pos.2 hdR
  have hsignSq : ‖signPoint (hypercubeSign s)‖ ^ 2 = (d : ℝ) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp_rw [signPoint_apply, hypercubeSign_sq]
    simp
  have hsign : ‖signPoint (hypercubeSign s)‖ = Real.sqrt d := by
    have hsqrtSq : (Real.sqrt d) ^ 2 = (d : ℝ) := Real.sq_sqrt hdR.le
    nlinarith [norm_nonneg (signPoint (hypercubeSign s)), Real.sqrt_nonneg d]
  rw [hypercubeDirection, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos hsqrt, hsign]
  exact inv_mul_cancel₀ hsqrt.ne'

/-- Scaling by `x ↦ x / h` converts the unit cutoff into the radius-`h`
cutoff exactly. -/
theorem radialCutoff_eq_profile_inv_smul
    (d : ℕ) (h : ℝ) (hh : 0 < h) (x : Point d) :
    radialCutoff d h hh x =
      smoothCutoffProfile (‖h⁻¹ • x‖ ^ 2) := by
  unfold radialCutoff
  congr 2
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hh]
  field_simp [hh.ne']

/-- Exact rescaling identity for the perturbation in the manuscript:
`f_s(x) = ‖x‖² - a h^beta F_s(x / h)`. -/
theorem hardValue_radialCutoff_eq_scaled_profile
    {d : ℕ} (s : Hypercube d) (a h beta : ℝ) (hh : 0 < h)
    (x : Point d) :
    hardValue (radialCutoff d h hh)
        ((a * h ^ (beta - 1)) / Real.sqrt d) (hypercubeSign s) x =
      ‖x‖ ^ 2 - a * h ^ beta * normalizedRadialProfile s (h⁻¹ • x) := by
  rw [hardValue, normalizedRadialProfile,
    radialCutoff_eq_profile_inv_smul, signedSum_smul,
    Real.rpow_sub_one hh.ne' beta]
  field_simp [hh.ne']

/-- Exact rescaling identity for the localized perturbation alone. -/
theorem hardPerturbation_radialCutoff_eq_scaled_profile
    {d : ℕ} (s : Hypercube d) (a h beta : ℝ) (hh : 0 < h)
    (x : Point d) :
    hardPerturbation (radialCutoff d h hh)
        ((a * h ^ (beta - 1)) / Real.sqrt d) (hypercubeSign s) x =
      (-a * h ^ beta) * normalizedRadialProfile s (h⁻¹ • x) := by
  unfold hardPerturbation normalizedRadialProfile
  rw [radialCutoff_eq_profile_inv_smul, signedSum_smul,
    Real.rpow_sub_one hh.ne' beta]
  field_simp [hh.ne']

/-- Exact scaling law for every iterated Fréchet derivative of the localized
perturbation. -/
theorem iteratedFDeriv_hardPerturbation_radialCutoff
    {d : ℕ} (s : Hypercube d) (a h beta : ℝ) (hh : 0 < h)
    (k : ℕ) (x : Point d) :
    iteratedFDeriv ℝ k
        (hardPerturbation (radialCutoff d h hh)
          ((a * h ^ (beta - 1)) / Real.sqrt d) (hypercubeSign s)) x =
      ((-a * h ^ beta) * (h⁻¹ ^ k)) •
        iteratedFDeriv ℝ k (normalizedRadialProfile s) (h⁻¹ • x) := by
  rw [show hardPerturbation (radialCutoff d h hh)
        ((a * h ^ (beta - 1)) / Real.sqrt d) (hypercubeSign s) =
      fun z : Point d ↦ (-a * h ^ beta) •
        normalizedRadialProfile s (h⁻¹ • z) by
      funext z
      simpa only [smul_eq_mul] using
        hardPerturbation_radialCutoff_eq_scaled_profile s a h beta hh z]
  let g : Point d → ℝ := fun z ↦ normalizedRadialProfile s (h⁻¹ • z)
  have hg : ContDiff ℝ k g :=
    (normalizedRadialProfile_contDiff s).comp
      (contDiff_id.const_smul h⁻¹)
  have hscale : iteratedFDeriv ℝ k g x =
      (h⁻¹ ^ k) •
        iteratedFDeriv ℝ k (normalizedRadialProfile s) (h⁻¹ • x) := by
    simpa only [g] using congrFun
      (iteratedFDeriv_comp_const_smul h⁻¹
        (normalizedRadialProfile_contDiff s)) x
  change iteratedFDeriv ℝ k (fun z ↦ (-a * h ^ beta) • g z) x = _
  rw [iteratedFDeriv_const_smul_apply' hg.contDiffAt, hscale, smul_smul]

/-- Norm form of the exact derivative scaling law, ready for quantitative
profile estimates. -/
theorem norm_iteratedFDeriv_hardPerturbation_sub
    {d : ℕ} (s : Hypercube d) (a h beta : ℝ) (hh : 0 < h)
    (k : ℕ) (x y : Point d) :
    ‖iteratedFDeriv ℝ k
          (hardPerturbation (radialCutoff d h hh)
            ((a * h ^ (beta - 1)) / Real.sqrt d) (hypercubeSign s)) x -
        iteratedFDeriv ℝ k
          (hardPerturbation (radialCutoff d h hh)
            ((a * h ^ (beta - 1)) / Real.sqrt d) (hypercubeSign s)) y‖ =
      |(-a * h ^ beta) * (h⁻¹ ^ k)| *
        ‖iteratedFDeriv ℝ k (normalizedRadialProfile s) (h⁻¹ • x) -
          iteratedFDeriv ℝ k (normalizedRadialProfile s) (h⁻¹ • y)‖ := by
  rw [iteratedFDeriv_hardPerturbation_radialCutoff,
    iteratedFDeriv_hardPerturbation_radialCutoff,
    ← smul_sub, norm_smul, Real.norm_eq_abs]

/-- Gradient-increment form of the exact scaling law. -/
theorem norm_gradient_hardPerturbation_radialCutoff_sub
    {d : ℕ} (s : Hypercube d) (a h beta : ℝ) (hh : 0 < h)
    (x y : Point d) :
    ‖∇ (hardPerturbation (radialCutoff d h hh)
          ((a * h ^ (beta - 1)) / Real.sqrt d) (hypercubeSign s)) x -
        ∇ (hardPerturbation (radialCutoff d h hh)
          ((a * h ^ (beta - 1)) / Real.sqrt d) (hypercubeSign s)) y‖ =
      |(-a * h ^ beta) * h⁻¹| *
        ‖∇ (normalizedRadialProfile s) (h⁻¹ • x) -
          ∇ (normalizedRadialProfile s) (h⁻¹ • y)‖ := by
  let p := hardPerturbation (radialCutoff d h hh)
    ((a * h ^ (beta - 1)) / Real.sqrt d) (hypercubeSign s)
  calc
    ‖∇ p x - ∇ p y‖ =
        ‖iteratedFDeriv ℝ 0 (∇ p) x -
          iteratedFDeriv ℝ 0 (∇ p) y‖ := by
      symm
      exact norm_iteratedFDeriv_zero_sub (∇ p) x y
    _ =
        ‖iteratedFDeriv ℝ 1 p x - iteratedFDeriv ℝ 1 p y‖ := by
      simpa only [Nat.zero_add] using
        norm_iteratedFDeriv_gradient_sub p x y (m := 0)
    _ = |(-a * h ^ beta) * h⁻¹| *
        ‖iteratedFDeriv ℝ 1 (normalizedRadialProfile s) (h⁻¹ • x) -
          iteratedFDeriv ℝ 1 (normalizedRadialProfile s) (h⁻¹ • y)‖ := by
      simpa only [pow_one] using
        norm_iteratedFDeriv_hardPerturbation_sub s a h beta hh 1 x y
    _ = |(-a * h ^ beta) * h⁻¹| *
        ‖∇ (normalizedRadialProfile s) (h⁻¹ • x) -
          ∇ (normalizedRadialProfile s) (h⁻¹ • y)‖ := by
      congr 1
      rw [← norm_iteratedFDeriv_gradient_sub
        (normalizedRadialProfile s) (h⁻¹ • x) (h⁻¹ • y) (m := 0)]
      simpa only using norm_iteratedFDeriv_zero_sub
        (∇ (normalizedRadialProfile s)) (h⁻¹ • x) (h⁻¹ • y)

end

end NoisyZO
