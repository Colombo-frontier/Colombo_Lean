import Bilevel.SmallGapLiftSupport
import Bilevel.Bowl
import Bilevel.Model
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
The actual three-dimensional clipped compensated small-gap lift.
All displayed gradients and Hessian blocks are derivatives of the displayed
objectives. Numerical smallness hypotheses are stated explicitly where used.
-/

noncomputable section

namespace Bilevel.SmallGapInstance

open scoped RealInnerProductSpace
open SmallGapProfiles SmallGapProfileBounds SmallGapLiftSupport

abbrev LowerSpace := EuclideanSpace ℝ (Fin 3)

def e0 : LowerSpace := EuclideanSpace.single 0 1
def e1 : LowerSpace := EuclideanSpace.single 1 1
def e2 : LowerSpace := EuclideanSpace.single 2 1
abbrev p0 : LowerSpace →L[ℝ] ℝ := EuclideanSpace.proj 0
abbrev p1 : LowerSpace →L[ℝ] ℝ := EuclideanSpace.proj 1
abbrev p2 : LowerSpace →L[ℝ] ℝ := EuclideanSpace.proj 2
def pack (u s z : ℝ) : LowerSpace := u • e0 + s • e1 + z • e2

@[simp] theorem pack_zero (u s z : ℝ) : pack u s z 0 = u := by simp [pack, e0, e1, e2]
@[simp] theorem pack_one (u s z : ℝ) : pack u s z 1 = s := by simp [pack, e0, e1, e2]
@[simp] theorem pack_two (u s z : ℝ) : pack u s z 2 = z := by simp [pack, e0, e1, e2]

theorem inner_pack (u s z : ℝ) (y : LowerSpace) :
    ⟪pack u s z, y⟫ = u * y 0 + s * y 1 + z * y 2 := by
  simp [pack, e0, e1, e2, inner_add_left, real_inner_smul_left, mul_comm]

theorem norm_sq (y : LowerSpace) :
    ‖y‖ ^ 2 = (y 0) ^ 2 + (y 1) ^ 2 + (y 2) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
  simp [Fin.sum_univ_succ, pow_two, real_inner_comm]
  ring

structure Parameters where
  μ : ℝ
  L : ℝ
  S : ℝ
  R : ℝ
  δ : ℝ
  μ_pos : 0 < μ
  L_pos : 0 < L
  S_pos : 0 < S
  R_pos : 0 < R
  δ_pos : 0 < δ
  μ_le_L : μ ≤ L
  width : 34 * δ ≤ R

namespace Parameters

variable (P : Parameters)

def residual (ω u : ℝ) : ℝ := r0 P.S P.R u - ω * r1 P.S P.δ u

def upper (x : ℝ) (y : LowerSpace) : ℝ := Bowl.value P.L x + P.L * y 1

def lower (ω x : ℝ) (y : LowerSpace) : ℝ :=
  P.μ / 2 * ((y 0) ^ 2 + (y 1) ^ 2) + P.L / 2 * (y 2) ^ 2 - P.L * x * y 0 -
    P.μ / P.L * (r0 P.S P.R (y 0) * normal P.R (y 1) -
      ω * r1 P.S P.δ (y 0) * normal P.δ (y 1)) +
    P.μ / (2 * P.L ^ 2) * (P.residual ω (y 0)) ^ 2

def lowerU (ω x : ℝ) (y : LowerSpace) : ℝ :=
  P.μ * y 0 - P.L * x - P.μ / P.L *
    (deriv (r0 P.S P.R) (y 0) * normal P.R (y 1) -
      ω * deriv (r1 P.S P.δ) (y 0) * normal P.δ (y 1)) +
    P.μ / P.L ^ 2 * P.residual ω (y 0) * deriv (P.residual ω) (y 0)

def lowerS (ω : ℝ) (y : LowerSpace) : ℝ :=
  P.μ * y 1 - P.μ / P.L *
    (r0 P.S P.R (y 0) * deriv (normal P.R) (y 1) -
      ω * r1 P.S P.δ (y 0) * deriv (normal P.δ) (y 1))

def upperX (x : ℝ) (_y : LowerSpace) : ℝ := Bowl.slope P.L x
def upperY (_x : ℝ) (_y : LowerSpace) : LowerSpace := pack 0 P.L 0
def lowerX (_ω _x : ℝ) (y : LowerSpace) : ℝ := -P.L * y 0
def lowerY (ω x : ℝ) (y : LowerSpace) : LowerSpace :=
  pack (P.lowerU ω x y) (P.lowerS ω y) (P.L * y 2)

def h00 (ω : ℝ) (y : LowerSpace) : ℝ :=
  P.μ - P.μ / P.L *
    (deriv (deriv (r0 P.S P.R)) (y 0) * normal P.R (y 1) -
      ω * deriv (deriv (r1 P.S P.δ)) (y 0) * normal P.δ (y 1)) +
    P.μ / P.L ^ 2 * ((deriv (P.residual ω) (y 0)) ^ 2 +
      P.residual ω (y 0) * deriv (deriv (P.residual ω)) (y 0))

def h01 (ω : ℝ) (y : LowerSpace) : ℝ :=
  -P.μ / P.L *
    (deriv (r0 P.S P.R) (y 0) * deriv (normal P.R) (y 1) -
      ω * deriv (r1 P.S P.δ) (y 0) * deriv (normal P.δ) (y 1))

def h11 (ω : ℝ) (y : LowerSpace) : ℝ :=
  P.μ - P.μ / P.L *
    (r0 P.S P.R (y 0) * deriv (deriv (normal P.R)) (y 1) -
      ω * r1 P.S P.δ (y 0) * deriv (deriv (normal P.δ)) (y 1))

def lowerYY (ω : ℝ) (y : LowerSpace) : LowerSpace →L[ℝ] LowerSpace :=
  ((P.h00 ω y) • p0 + (P.h01 ω y) • p1).smulRight e0 +
  ((P.h01 ω y) • p0 + (P.h11 ω y) • p1).smulRight e1 +
  (P.L • p2).smulRight e2

def lowerXY : LowerSpace →L[ℝ] ℝ := (-P.L) • p0

theorem residual_contDiff (ω : ℝ) : ContDiff ℝ 3 (P.residual ω) :=
  (r0_contDiff P.S P.R).sub (contDiff_const.mul (r1_contDiff P.S P.δ))

theorem residual_hasDerivAt (ω u : ℝ) :
    HasDerivAt (P.residual ω) (deriv (P.residual ω) u) u :=
  ((P.residual_contDiff ω).differentiable (by norm_num) u).hasDerivAt

theorem residual_deriv (ω u : ℝ) :
    deriv (P.residual ω) u = deriv (r0 P.S P.R) u - ω * deriv (r1 P.S P.δ) u := by
  exact (((r0_contDiff P.S P.R).differentiable (by norm_num) u).hasDerivAt.sub
    (((r1_contDiff P.S P.δ).differentiable (by norm_num) u).hasDerivAt.const_mul ω)).deriv

theorem upper_hasGradientX (x : ℝ) (y : LowerSpace) :
    HasGradientAt (fun x => P.upper x y) (P.upperX x y) x :=
  ((Bowl.hasDerivAt_value P.L x).add_const (P.L * y 1)).hasGradientAt'

theorem upper_hasGradientY (x : ℝ) (y : LowerSpace) :
    HasGradientAt (P.upper x) (P.upperY x y) y := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert ((p1.hasFDerivAt (x := y)).const_mul P.L).const_add (Bowl.value P.L x) using 1
  ext v
  simp [upperY, InnerProductSpace.toDual_apply, inner_pack, Fin.sum_univ_succ]
  ring

theorem lower_hasGradientX (ω x : ℝ) (y : LowerSpace) :
    HasGradientAt (fun x => P.lower ω x y) (P.lowerX ω x y) x := by
  have h := (((hasDerivAt_id x).const_mul P.L).mul_const (y 0)).const_sub
    (P.μ / 2 * ((y 0) ^ 2 + (y 1) ^ 2) + P.L / 2 * (y 2) ^ 2)
  have h' := (h.sub_const (P.μ / P.L * (r0 P.S P.R (y 0) * normal P.R (y 1) -
    ω * r1 P.S P.δ (y 0) * normal P.δ (y 1)))).add_const
      (P.μ / (2 * P.L ^ 2) * (P.residual ω (y 0)) ^ 2)
  convert h'.hasGradientAt' using 1
  simp [lowerX]

theorem lower_hasGradientY (ω x : ℝ) (y : LowerSpace) :
    HasGradientAt (P.lower ω x) (P.lowerY ω x y) y := by
  have h0 := p0.hasFDerivAt (x := y)
  have h1 := p1.hasFDerivAt (x := y)
  have h2 := p2.hasFDerivAt (x := y)
  have hr0 := ((r0_contDiff P.S P.R).differentiable (by norm_num) (y 0)).hasDerivAt.hasFDerivAt.comp y h0
  have hr1 := ((r1_contDiff P.S P.δ).differentiable (by norm_num) (y 0)).hasDerivAt.hasFDerivAt.comp y h0
  have hq0 := ((normal_contDiff P.R P.R_pos).differentiable (by norm_num) (y 1)).hasDerivAt.hasFDerivAt.comp y h1
  have hq1 := ((normal_contDiff P.δ P.δ_pos).differentiable (by norm_num) (y 1)).hasDerivAt.hasFDerivAt.comp y h1
  have hr := (P.residual_hasDerivAt ω (y 0)).hasFDerivAt.comp y h0
  have h := (((((h0.mul h0).add (h1.mul h1)).const_mul (P.μ / 2)).add
    ((h2.mul h2).const_mul (P.L / 2))).sub (h0.const_mul (P.L * x))).sub
      (((hr0.mul hq0).sub ((hr1.const_mul ω).mul hq1)).const_mul (P.μ / P.L)) |>.add
        ((hr.mul hr).const_mul (P.μ / (2 * P.L ^ 2)))
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert h using 1
  · funext v
    simp only [lower, pow_two, Function.comp_apply]
    rfl
  ext v
  simp [lowerY, lowerU, lowerS, InnerProductSpace.toDual_apply, inner_pack, Fin.sum_univ_succ]
  ring

theorem lowerX_hasFDerivAt (ω x : ℝ) (y : LowerSpace) :
    HasFDerivAt (P.lowerX ω x) P.lowerXY y :=
  (p0.hasFDerivAt (x := y)).const_mul (-P.L)

theorem lowerU_hasFDerivAt (ω x : ℝ) (y : LowerSpace) :
    HasFDerivAt (P.lowerU ω x) ((P.h00 ω y) • p0 + (P.h01 ω y) • p1) y := by
  have h0 := p0.hasFDerivAt (x := y)
  have h1 := p1.hasFDerivAt (x := y)
  have hr0 := (deriv_hasDerivAt (r0_contDiff P.S P.R) (y 0)).hasFDerivAt.comp y h0
  have hr1 := (deriv_hasDerivAt (r1_contDiff P.S P.δ) (y 0)).hasFDerivAt.comp y h0
  have hq0 := ((normal_contDiff P.R P.R_pos).differentiable (by norm_num) (y 1)).hasDerivAt.hasFDerivAt.comp y h1
  have hq1 := ((normal_contDiff P.δ P.δ_pos).differentiable (by norm_num) (y 1)).hasDerivAt.hasFDerivAt.comp y h1
  have hr := (P.residual_hasDerivAt ω (y 0)).hasFDerivAt.comp y h0
  have hdr := (deriv_hasDerivAt (P.residual_contDiff ω) (y 0)).hasFDerivAt.comp y h0
  have h := (((h0.const_mul P.μ).sub_const (P.L * x)).sub
    (((hr0.mul hq0).sub ((hr1.const_mul ω).mul hq1)).const_mul (P.μ / P.L))).add
      ((hr.const_mul (P.μ / P.L ^ 2)).mul hdr)
  convert h using 1
  ext v
  simp [h00, h01]
  ring

theorem lowerS_hasFDerivAt (ω : ℝ) (y : LowerSpace) :
    HasFDerivAt (P.lowerS ω) ((P.h01 ω y) • p0 + (P.h11 ω y) • p1) y := by
  have h0 := p0.hasFDerivAt (x := y)
  have h1 := p1.hasFDerivAt (x := y)
  have hr0 := ((r0_contDiff P.S P.R).differentiable (by norm_num) (y 0)).hasDerivAt.hasFDerivAt.comp y h0
  have hr1 := ((r1_contDiff P.S P.δ).differentiable (by norm_num) (y 0)).hasDerivAt.hasFDerivAt.comp y h0
  have hq0 := (deriv_hasDerivAt (normal_contDiff P.R P.R_pos) (y 1)).hasFDerivAt.comp y h1
  have hq1 := (deriv_hasDerivAt (normal_contDiff P.δ P.δ_pos) (y 1)).hasFDerivAt.comp y h1
  have h := (h1.const_mul P.μ).sub
    (((hr0.mul hq0).sub ((hr1.const_mul ω).mul hq1)).const_mul (P.μ / P.L))
  convert h using 1
  ext v
  simp [h01, h11]
  ring

theorem lowerY_hasFDerivAt (ω x : ℝ) (y : LowerSpace) :
    HasFDerivAt (P.lowerY ω x) (P.lowerYY ω y) y := by
  exact (((P.lowerU_hasFDerivAt ω x y).smul_const e0).add
    ((P.lowerS_hasFDerivAt ω y).smul_const e1)).add
      (((p2.hasFDerivAt (x := y)).const_mul P.L).smul_const e2)

theorem lowerYY_apply (ω : ℝ) (y v : LowerSpace) :
    P.lowerYY ω y v = pack (P.h00 ω y * v 0 + P.h01 ω y * v 1)
      (P.h01 ω y * v 0 + P.h11 ω y * v 1) (P.L * v 2) := by
  simp [lowerYY, pack]

theorem lower_contDiff (ω x : ℝ) : ContDiff ℝ 3 (P.lower ω x) := by
  have h0 : ContDiff ℝ 3 (fun y : LowerSpace => y 0) := p0.contDiff
  have h1 : ContDiff ℝ 3 (fun y : LowerSpace => y 1) := p1.contDiff
  have h2 : ContDiff ℝ 3 (fun y : LowerSpace => y 2) := p2.contDiff
  exact (((contDiff_const.mul ((h0.pow 2).add (h1.pow 2))).add
    (contDiff_const.mul (h2.pow 2))).sub (contDiff_const.mul h0) |>.sub
      (contDiff_const.mul (((r0_contDiff P.S P.R).comp h0).mul
        ((normal_contDiff P.R P.R_pos).comp h1) |>.sub
          ((contDiff_const.mul ((r1_contDiff P.S P.δ).comp h0)).mul
            ((normal_contDiff P.δ P.δ_pos).comp h1))))) |>.add
              (contDiff_const.mul (((P.residual_contDiff ω).comp h0).pow 2))

theorem delta_le_R : P.δ ≤ P.R := by linarith [P.width, P.δ_pos]

theorem residual_abs_bound (ω u : ℝ) (hω : |ω| ≤ 1) :
    |P.residual ω u| ≤ 36 * P.S * P.R ^ 2 := by
  have h0 := r0_abs_bound P.S P.R u P.S_pos.le
  have h1 := r1_abs_bound P.S P.δ u P.S_pos.le
  have hw : |ω * r1 P.S P.δ u| ≤ |r1 P.S P.δ u| := by
    rw [abs_mul]
    nlinarith [mul_le_mul_of_nonneg_right hω (abs_nonneg (r1 P.S P.δ u))]
  have hsq : P.δ ^ 2 ≤ P.R ^ 2 := by nlinarith [P.delta_le_R, P.δ_pos, P.R_pos]
  have hm := mul_le_mul_of_nonneg_left hsq P.S_pos.le
  have ht := abs_sub (r0 P.S P.R u) (ω * r1 P.S P.δ u)
  change |r0 P.S P.R u - ω * r1 P.S P.δ u| ≤ _
  nlinarith

theorem residual_abs_bound_fine (ω u : ℝ) (hω : |ω| ≤ 1)
    (hu : |u| ≤ 34 * P.δ) : |P.residual ω u| ≤ 612 * P.S * P.δ ^ 2 := by
  have hcore := r0_core P.S P.R u P.R_pos (hu.trans P.width)
  have hu2 : u ^ 2 ≤ 1156 * P.δ ^ 2 := by
    nlinarith [sq_abs u, abs_nonneg u, P.δ_pos]
  have hmul := mul_le_mul_of_nonneg_left hu2 P.S_pos.le
  have h0 : |r0 P.S P.R u| ≤ 578 * P.S * P.δ ^ 2 := by
    rw [hcore, abs_of_nonneg (div_nonneg (mul_nonneg P.S_pos.le (sq_nonneg u)) (by norm_num))]
    nlinarith
  have h1 := r1_abs_bound P.S P.δ u P.S_pos.le
  have hw : |ω * r1 P.S P.δ u| ≤ |r1 P.S P.δ u| := by
    rw [abs_mul]
    nlinarith [mul_le_mul_of_nonneg_right hω (abs_nonneg (r1 P.S P.δ u))]
  have ht := abs_sub (r0 P.S P.R u) (ω * r1 P.S P.δ u)
  change |r0 P.S P.R u - ω * r1 P.S P.δ u| ≤ _
  linarith

/-- Explicit numerical versions of the two core smallness requirements. -/
structure CoreSmallness : Prop where
  coarse : 36 * P.S * P.R ≤ P.L / 4
  fine : 612 * P.S * P.δ ≤ P.L / 4

theorem coarse_response_core (ω u : ℝ) (hω : |ω| ≤ 1) (hsmall : P.CoreSmallness) :
    |P.residual ω u / P.L| ≤ P.R / 4 := by
  rw [abs_div, abs_of_pos P.L_pos]
  apply (div_le_iff₀ P.L_pos).mpr
  have h := mul_le_mul_of_nonneg_right hsmall.coarse P.R_pos.le
  nlinarith [P.residual_abs_bound ω u hω]

theorem fine_response_core (ω u : ℝ) (hω : |ω| ≤ 1) (hsmall : P.CoreSmallness)
    (hu : |u| ≤ 34 * P.δ) : |P.residual ω u / P.L| ≤ P.δ / 4 := by
  rw [abs_div, abs_of_pos P.L_pos]
  apply (div_le_iff₀ P.L_pos).mpr
  have h := mul_le_mul_of_nonneg_right hsmall.fine P.δ_pos.le
  nlinarith [P.residual_abs_bound_fine ω u hω hu]

theorem normal_coarse_at_response (ω u : ℝ) (hω : |ω| ≤ 1) (hsmall : P.CoreSmallness) :
    normal P.R (P.residual ω u / P.L) = P.residual ω u / P.L ∧
      deriv (normal P.R) (P.residual ω u / P.L) = 1 := by
  have hs := P.coarse_response_core ω u hω hsmall
  exact ⟨normal_core _ _ P.R_pos hs, normal_deriv_core _ _ P.R_pos hs⟩

theorem fine_products_at_response (ω u : ℝ) (hω : |ω| ≤ 1) (hsmall : P.CoreSmallness) :
    r1 P.S P.δ u * normal P.δ (P.residual ω u / P.L) =
        r1 P.S P.δ u * (P.residual ω u / P.L) ∧
    deriv (r1 P.S P.δ) u * normal P.δ (P.residual ω u / P.L) =
        deriv (r1 P.S P.δ) u * (P.residual ω u / P.L) ∧
    r1 P.S P.δ u * deriv (normal P.δ) (P.residual ω u / P.L) = r1 P.S P.δ u := by
  by_cases hu : |u| ≤ 34 * P.δ
  · have hs := P.fine_response_core ω u hω hsmall hu
    simp only [normal_core _ _ P.δ_pos hs, normal_deriv_core _ _ P.δ_pos hs, mul_one,
      and_self]
  · have hs := le_of_not_ge hu
    simp only [r1_zero _ _ _ P.δ_pos hs, r1_deriv_zero _ _ _ P.δ_pos hs, zero_mul,
      and_self]

def response (ω x : ℝ) : LowerSpace :=
  pack (P.L / P.μ * x) (P.residual ω (P.L / P.μ * x) / P.L) 0

theorem response_stationary (ω x : ℝ) (hω : |ω| ≤ 1) (hsmall : P.CoreSmallness) :
    P.lowerY ω x (P.response ω x) = 0 := by
  have hc := P.normal_coarse_at_response ω (P.L / P.μ * x) hω hsmall
  have hf := P.fine_products_at_response ω (P.L / P.μ * x) hω hsmall
  have hu : P.lowerU ω x (P.response ω x) = 0 := by
    simp only [lowerU, response, pack_zero, pack_one, hc.1, P.residual_deriv,
      mul_assoc ω (deriv (r1 P.S P.δ) (P.L / P.μ * x))]
    rw [hf.2.1]
    field_simp [P.μ_pos.ne', P.L_pos.ne']
    ring
  have hs : P.lowerS ω (P.response ω x) = 0 := by
    simp only [lowerS, response, pack_zero, pack_one, hc.2, mul_one,
      mul_assoc ω (r1 P.S P.δ (P.L / P.μ * x))]
    rw [hf.2.2]
    simp only [residual]
    ring
  rw [lowerY, hu, hs]
  have hz : P.response ω x 2 = 0 := pack_two _ _ _
  rw [hz, mul_zero]
  simp [pack]

theorem response_zero (ω : ℝ) : P.response ω 0 = 0 := by
  have hp : phi 0 = 0 := by simpa using phi_core 0 (by norm_num)
  have hs : psi 0 = 0 := by simpa using psi_core 0 (by norm_num)
  simp [response, residual, r0, r1, hp, hs, pack]

theorem upper_response (ω x : ℝ) :
    P.upper x (P.response ω x) = Bowl.value P.L x +
      r0 P.S P.R (P.L / P.μ * x) - ω * r1 P.S P.δ (P.L / P.μ * x) := by
  simp only [upper, response, pack_one, residual]
  field_simp [P.L_pos.ne']
  ring

end Parameters
end Bilevel.SmallGapInstance
