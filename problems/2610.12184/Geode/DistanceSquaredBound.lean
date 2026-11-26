import Geode.GeodesicLine
import Geode.SquaredDistanceScalar
import Geode.FiniteTaylor
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Squared-distance upper bound on actual hyperbolic geodesics

The proof integrates the scalar second derivative bound and removes a positive
inverse-cosh regularization. The radius bound is the only geometric hypothesis.
-/

namespace Geode.Lorentz

open Filter Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def radialCosh (A : GeodesicLine E) (p : Point E) (t : ℝ) : ℝ :=
  -form E (A.point t).val p.val

noncomputable def radialCoshSlope (A : GeodesicLine E) (p : Point E) (t : ℝ) : ℝ :=
  -form E (A.velocity t) p.val

theorem hasDerivAt_radialCosh (A : GeodesicLine E) (p : Point E) (t : ℝ) :
    HasDerivAt (radialCosh A p) (radialCoshSlope A p t) t := by
  have h := (hasDerivAt_form (A.position_deriv t) (hasDerivAt_const t p.val)).neg
  simpa only [radialCosh, radialCoshSlope, form_zero_right, add_zero] using h

theorem hasDerivAt_radialCoshSlope (A : GeodesicLine E) (p : Point E) (t : ℝ) :
    HasDerivAt (radialCoshSlope A p) (A.speedSq * radialCosh A p t) t := by
  have h := (hasDerivAt_form (A.velocity_deriv t) (hasDerivAt_const t p.val)).neg
  simpa only [radialCosh, radialCoshSlope, form_zero_right, form_smul_left,
    add_zero, mul_neg] using h

theorem squaredArcoshSlope_form (z p : Point E) (u : Ambient E)
    (hu : form E z.val u = 0) :
    Geode.squaredArcoshSlope (-form E z.val p.val) * (-form E u p.val) =
      -form E (logMap z p) u := by
  have hd : Geode.arcosh (-form E z.val p.val) = dist z p := rfl
  have hs : Real.sqrt ((-form E z.val p.val) ^ 2 - 1) = Real.sinh (dist z p) :=
    (Geode.sinh_arcosh _).symm
  rw [Geode.squaredArcoshSlope, hd, hs, logMap, direction,
    form_smul_left, form_smul_left, form_sub_left, form_smul_left, hu]
  rw [form_comm p.val u]
  ring

theorem regularized_line_taylor (A : GeodesicLine E) (p : Point E) {M D : ℝ}
    (hM : 0 < M) (hMD : M < D)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, dist (A.point t) p ≤ M) :
    Geode.squaredArcosh (radialCosh A p 1 + (Real.cosh D - Real.cosh M)) ≤
      Geode.squaredArcosh (radialCosh A p 0 + (Real.cosh D - Real.cosh M)) +
      Geode.squaredArcoshSlope (radialCosh A p 0 + (Real.cosh D - Real.cosh M)) *
        radialCoshSlope A p 0 + A.speedSq * Geode.curvatureFactor D / 2 := by
  let δ := Real.cosh D - Real.cosh M
  have hD : 0 < D := hM.trans hMD
  have hδ : 0 < δ := by
    apply sub_pos.mpr
    apply Real.cosh_lt_cosh.mpr
    simpa only [abs_of_pos hM, abs_of_pos hD] using hMD
  have hF : ∀ t, 1 ≤ radialCosh A p t := fun t => reverse_cauchy (A.point t) p
  have hz : ∀ t, 1 < radialCosh A p t + δ := fun t => by linarith [hF t]
  have hs : 0 ≤ A.speedSq := by
    rw [← A.norm_sq 0]
    exact tangent_nonneg (A.point 0) (A.tangent 0)
  let f := fun t => Geode.squaredArcosh (radialCosh A p t + δ)
  let g := fun t => Geode.squaredArcoshSlope (radialCosh A p t + δ) * radialCoshSlope A p t
  let h := fun t => Geode.squaredArcoshSlopeDerivative (radialCosh A p t + δ) *
      radialCoshSlope A p t ^ 2 + Geode.squaredArcoshSlope (radialCosh A p t + δ) *
      (A.speedSq * radialCosh A p t)
  apply Geode.finite_taylor_upper f g h (A.speedSq * Geode.curvatureFactor D)
    (fun t => Geode.hasDerivAt_squaredArcosh_comp (hasDerivAt_radialCosh A p t) (hz t))
    (fun t => Geode.hasDerivAt_squaredArcosh_comp_slope
      (hasDerivAt_radialCosh A p t) (hasDerivAt_radialCoshSlope A p t) (hz t))
  intro t ht
  have hFbound : radialCosh A p t ≤ Real.cosh M := by
    have hc := Real.cosh_le_cosh.mpr (show |dist (A.point t) p| ≤ |M| by
      simpa only [abs_of_nonneg dist_nonneg, abs_of_pos hM] using hbound t ht)
    simpa only [cosh_dist, radialCosh] using hc
  have hb : radialCosh A p t + δ ≤ Real.cosh D := by dsimp [δ]; linarith
  have hh := Geode.squaredArcosh_second_bound_uniform (g := radialCoshSlope A p t)
    (a := Real.sqrt A.speedSq) (hF t) hδ hD hb
  rw [Real.sq_sqrt hs] at hh
  exact hh

/-- The actual curvature-controlled Taylor inequality, including geodesics
passing through the reference point. -/
theorem distance_sq_line_upper (A : GeodesicLine E) (p : Point E) {M : ℝ}
    (hM : 0 < M)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, dist (A.point t) p ≤ M) :
    dist (A.point 1) p ^ 2 ≤ dist (A.point 0) p ^ 2 -
      2 * form E (logMap (A.point 0) p) (A.velocity 0) +
      Geode.curvatureFactor M * A.speedSq := by
  let D : ℕ → ℝ := fun n => M + 1 / ((n : ℝ) + 1)
  let δ : ℕ → ℝ := fun n => Real.cosh (D n) - Real.cosh M
  have hDn : ∀ n, M < D n := fun n => by
    dsimp [D]
    exact lt_add_of_pos_right M (by positivity)
  have hDlim : Tendsto D atTop (𝓝 M) := by
    simpa only [add_zero] using
      (tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto D atTop (𝓝 (M + 0)))
  have hδlim : Tendsto δ atTop (𝓝 0) := by
    simpa only [sub_self] using
      ((Real.continuous_cosh.tendsto M).comp hDlim).sub_const (Real.cosh M)
  have hcont : Continuous Geode.squaredArcosh :=
    (Geode.continuous_arcosh.pow 2).div_const 2
  have hflim (t : ℝ) :
      Tendsto (fun n => Geode.squaredArcosh (radialCosh A p t + δ n))
        atTop (𝓝 (Geode.squaredArcosh (radialCosh A p t))) := by
    apply hcont.continuousAt.tendsto.comp
    simpa only [add_zero] using tendsto_const_nhds.add hδlim
  have hglim : Tendsto
      (fun n => Geode.squaredArcoshSlope (radialCosh A p 0 + δ n) * radialCoshSlope A p 0)
      atTop (𝓝 (Geode.squaredArcoshSlope (radialCosh A p 0) * radialCoshSlope A p 0)) := by
    by_cases heq : A.point 0 = p
    · have hg0 : radialCoshSlope A p 0 = 0 := by
        dsimp [radialCoshSlope]
        rw [← heq, form_comm, A.tangent 0, neg_zero]
      simp only [hg0, mul_zero]
      exact tendsto_const_nhds
    · have hgt : 1 < radialCosh A p 0 := by
        apply lt_of_le_of_ne (reverse_cauchy (A.point 0) p)
        intro h
        exact heq ((reverse_cauchy_eq_iff (A.point 0) p).mp h.symm)
      have hs := (Geode.hasDerivAt_squaredArcoshSlope hgt).continuousAt.tendsto.comp
        (show Tendsto (fun n => radialCosh A p 0 + δ n) atTop (𝓝 (radialCosh A p 0)) by
          simpa only [add_zero] using tendsto_const_nhds.add hδlim)
      exact hs.mul_const _
  have hζlim : Tendsto (fun n => Geode.curvatureFactor (D n)) atTop
      (𝓝 (Geode.curvatureFactor M)) :=
    (Geode.hasDerivAt_curvatureFactor hM).continuousAt.tendsto.comp hDlim
  have hineq := le_of_tendsto_of_tendsto' (hflim 1)
    (((hflim 0).add hglim).add ((hζlim.const_mul A.speedSq).div_const 2))
    (fun n => regularized_line_taylor A p hM (hDn n) hbound)
  have hcoef := squaredArcoshSlope_form (A.point 0) p (A.velocity 0) (A.tangent 0)
  change Geode.squaredArcoshSlope (radialCosh A p 0) * radialCoshSlope A p 0 =
    -form E (logMap (A.point 0) p) (A.velocity 0) at hcoef
  rw [hcoef] at hineq
  change dist (A.point 1) p ^ 2 / 2 ≤ dist (A.point 0) p ^ 2 / 2 +
    -form E (logMap (A.point 0) p) (A.velocity 0) +
    A.speedSq * Geode.curvatureFactor M / 2 at hineq
  nlinarith

end Geode.Lorentz
