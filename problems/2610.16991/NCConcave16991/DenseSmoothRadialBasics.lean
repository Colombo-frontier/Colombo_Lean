/- Adapted from the proved radial-calculus fragments in ../0105_formalization/Manuscript0105/RadialBasics.lean. No assumed lower bounds are imported. -/
import NCConcave16991.ConePrimitives
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Basic bounds for the radial lower-bound chain

This file proves the strict range bound for the radial coordinate and the abstract finite-chain
estimate underlying Lemma `lem:base-gap`.
-/

open scoped BigOperators InnerProductSpace Real

namespace NCConcave16991.DenseSmooth

section RadialCoordinate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The manuscript's dimension-free radial coordinate. -/
noncomputable def radialCoordinate (u x : E) : ℝ :=
  ⟪u, x⟫_ℝ / Real.sqrt (1 + ‖x‖ ^ 2)

/-- Equivalent power-form coordinate, convenient for differentiation. -/
noncomputable def radialCoordinatePow (u x : E) : ℝ :=
  (1 + ‖x‖ ^ 2) ^ (-(1 / 2 : ℝ)) * ⟪u, x⟫_ℝ

/-- Gradient formula for the radial coordinate in power form. -/
noncomputable def radialCoordinateGradient (u x : E) : E :=
  (1 + ‖x‖ ^ 2) ^ (-(1 / 2 : ℝ)) • u -
    (⟪u, x⟫_ℝ * (1 + ‖x‖ ^ 2) ^ (-(3 / 2 : ℝ))) • x

theorem hasFDerivAt_radialCoordinatePow (u x : E) :
    HasFDerivAt (radialCoordinatePow u)
      (innerSL ℝ (radialCoordinateGradient u x)) x := by
  have hbase : HasFDerivAt (fun z : E ↦ 1 + ‖z‖ ^ 2)
      (2 • innerSL ℝ x) x := by
    simpa using ((hasFDerivAt_id x).norm_sq).const_add 1
  have hpos : 0 < 1 + ‖x‖ ^ 2 := by positivity
  have hpow := hbase.rpow_const (p := -(1 / 2 : ℝ)) (Or.inl hpos.ne')
  have hinner : HasFDerivAt (fun z : E ↦ ⟪u, z⟫_ℝ) (innerSL ℝ u) x :=
    (innerSL ℝ u).hasFDerivAt
  convert hpow.mul hinner using 1
  · funext z
    rfl
  · ext z
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      innerSL_apply_apply, inner_sub_left, real_inner_smul_left]
    dsimp [radialCoordinateGradient]
    simp only [inner_sub_left, real_inner_smul_left]
    ring_nf

theorem radialCoordinatePow_eq (u x : E) :
    radialCoordinatePow u x = radialCoordinate u x := by
  rw [radialCoordinatePow, radialCoordinate, Real.sqrt_eq_rpow,
    Real.rpow_neg (by positivity : 0 ≤ 1 + ‖x‖ ^ 2)]
  ring

theorem hasFDerivAt_radialCoordinate (u x : E) :
    HasFDerivAt (radialCoordinate u)
      (innerSL ℝ (radialCoordinateGradient u x)) x := by
  convert hasFDerivAt_radialCoordinatePow u x using 1
  funext z
  exact (radialCoordinatePow_eq u z).symm

/-- A unit-direction radial coordinate always lies strictly between `-1` and `1`. -/
theorem abs_radialCoordinate_lt_one {u : E} (hu : ‖u‖ = 1) (x : E) :
    |radialCoordinate u x| < 1 := by
  have hbase : 0 < 1 + ‖x‖ ^ 2 := by positivity
  have hden : 0 < Real.sqrt (1 + ‖x‖ ^ 2) := Real.sqrt_pos.2 hbase
  have hnormlt : ‖x‖ < Real.sqrt (1 + ‖x‖ ^ 2) := by
    have h := Real.sqrt_lt_sqrt (sq_nonneg ‖x‖) (by linarith : ‖x‖ ^ 2 < 1 + ‖x‖ ^ 2)
    simpa using h
  have hinner : |⟪u, x⟫_ℝ| ≤ ‖x‖ := by
    calc
      |⟪u, x⟫_ℝ| ≤ ‖u‖ * ‖x‖ := abs_real_inner_le_norm _ _
      _ = ‖x‖ := by rw [hu, one_mul]
  rw [radialCoordinate, abs_div, abs_of_pos hden]
  exact (div_lt_one hden).2 (hinner.trans_lt hnormlt)

end RadialCoordinate

section ChainGap

/-- An abstract form of the radial average chain: one initial coordinate, `T` gated links, and a
nonnegative quadratic contribution. -/
def abstractRadialChain {T : ℕ} (q : Fin (T + 1) → ℝ) (gate : Fin T → ℝ)
    (quadratic : ℝ) : ℝ :=
  -q 0 - ∑ j, gate j * (q j.succ + 1) + quadratic

/-- Each gated link is at most two when both the gate and radial coordinate lie in `[0,1]` and
`[-1,1]`, respectively. -/
theorem gated_link_le_two {g q : ℝ} (hg0 : 0 ≤ g) (hg1 : g ≤ 1)
    (hq0 : -1 ≤ q) (hq1 : q ≤ 1) :
    g * (q + 1) ≤ 2 := by
  have hqnonneg : 0 ≤ q + 1 := by linarith
  calc
    g * (q + 1) ≤ 1 * (q + 1) := mul_le_mul_of_nonneg_right hg1 hqnonneg
    _ ≤ 2 := by linarith

/-- Initial-gap lower estimate for the abstract radial chain.  This proves the manuscript's
`R(x) ≥ -1 - 2T`, hence in particular `R(x) ≥ -2(T+1)`. -/
theorem abstractRadialChain_lower {T : ℕ}
    (q : Fin (T + 1) → ℝ) (gate : Fin T → ℝ) (quadratic : ℝ)
    (hq : ∀ j, |q j| ≤ 1) (hgate : ∀ j, gate j ∈ Set.Icc (0 : ℝ) 1)
    (hquad : 0 ≤ quadratic) :
    -1 - 2 * (T : ℝ) ≤ abstractRadialChain q gate quadratic := by
  have hq0 : q 0 ≤ 1 := (abs_le.mp (hq 0)).2
  have hlink (j : Fin T) : gate j * (q j.succ + 1) ≤ 2 := by
    exact gated_link_le_two (hgate j).1 (hgate j).2
      (abs_le.mp (hq j.succ)).1 (abs_le.mp (hq j.succ)).2
  have hsum : (∑ j, gate j * (q j.succ + 1)) ≤ 2 * (T : ℝ) := by
    calc
      (∑ j, gate j * (q j.succ + 1)) ≤ ∑ _j : Fin T, (2 : ℝ) :=
        Finset.sum_le_sum fun j _ ↦ hlink j
      _ = 2 * (T : ℝ) := by simp; ring
  dsimp [abstractRadialChain]
  linarith

theorem abstractRadialChain_zero {T : ℕ} :
    abstractRadialChain (fun _ : Fin (T + 1) ↦ 0) (fun _ : Fin T ↦ 0) 0 = 0 := by
  simp [abstractRadialChain]

end ChainGap

end NCConcave16991.DenseSmooth
