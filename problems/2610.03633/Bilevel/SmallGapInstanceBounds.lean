import Bilevel.SmallGapInstance
import Bilevel.HessianLowerBound

/-! Actual global Hessian bounds and lower minimization for the clipped small-gap lift. -/

noncomputable section
namespace Bilevel.SmallGapInstance.Parameters

open scoped RealInnerProductSpace
open SmallGapProfiles SmallGapProfileBounds SmallGapLiftSupport

variable (P : Parameters)

theorem residual_deriv2 (ω u : ℝ) :
    deriv (deriv (P.residual ω)) u =
      deriv (deriv (r0 P.S P.R)) u - ω * deriv (deriv (r1 P.S P.δ)) u := by
  have he : deriv (P.residual ω) = fun v =>
      deriv (r0 P.S P.R) v - ω * deriv (r1 P.S P.δ) v := funext (P.residual_deriv ω)
  rw [he]
  exact ((deriv_hasDerivAt (r0_contDiff P.S P.R) u).sub
    ((deriv_hasDerivAt (r1_contDiff P.S P.δ) u).const_mul ω)).deriv

theorem residual_jet_bounds (ω u : ℝ) (hω : |ω| ≤ 1) :
    |P.residual ω u| ≤ C * P.S * (P.R ^ 2 + P.δ ^ 2) ∧
    |deriv (P.residual ω) u| ≤ C * P.S * (P.R + P.δ) ∧
    |deriv (deriv (P.residual ω)) u| ≤ 2 * C * P.S := by
  have h0 := r0_jet_bounds P.S P.R u P.S_pos P.R_pos
  have h1 := r1_jet_bounds P.S P.δ u P.S_pos P.δ_pos
  constructor
  · change |r0 P.S P.R u - ω * r1 P.S P.δ u| ≤ _
    convert abs_signed_sub_le h0.1 h1.1 hω using 1
    ring
  constructor
  · rw [P.residual_deriv]
    convert abs_signed_sub_le h0.2.1 h1.2.1 hω using 1
    ring
  · rw [P.residual_deriv2]
    convert abs_signed_sub_le h0.2.2 h1.2.2 hω using 1
    ring

theorem coupling_bounds (ω : ℝ) (y : LowerSpace) (hω : |ω| ≤ 1) :
    |deriv (deriv (r0 P.S P.R)) (y 0) * normal P.R (y 1) -
      ω * deriv (deriv (r1 P.S P.δ)) (y 0) * normal P.δ (y 1)| ≤ C ^ 2 * P.S * (P.R + P.δ) ∧
    |deriv (r0 P.S P.R) (y 0) * deriv (normal P.R) (y 1) -
      ω * deriv (r1 P.S P.δ) (y 0) * deriv (normal P.δ) (y 1)| ≤ C ^ 2 * P.S * (P.R + P.δ) ∧
    |r0 P.S P.R (y 0) * deriv (deriv (normal P.R)) (y 1) -
      ω * r1 P.S P.δ (y 0) * deriv (deriv (normal P.δ)) (y 1)| ≤ C ^ 2 * P.S * (P.R + P.δ) := by
  have h0 := coupling_jet_bounds P.S P.R (y 0) (y 1) P.S_pos P.R_pos
    (r0_jet_bounds P.S P.R (y 0) P.S_pos P.R_pos)
  have h1 := coupling_jet_bounds P.S P.δ (y 0) (y 1) P.S_pos P.δ_pos
    (r1_jet_bounds P.S P.δ (y 0) P.S_pos P.δ_pos)
  constructor
  · convert abs_signed_sub_le h0.1 h1.1 hω using 1 <;> ring
  constructor
  · convert abs_signed_sub_le h0.2.1 h1.2.1 hω using 1 <;> ring
  · convert abs_signed_sub_le h0.2.2 h1.2.2 hω using 1 <;> ring

theorem compensation_bound (ω u : ℝ) (hω : |ω| ≤ 1) :
    |(deriv (P.residual ω) u) ^ 2 + P.residual ω u * deriv (deriv (P.residual ω)) u| ≤
      C ^ 2 * P.S ^ 2 * ((P.R + P.δ) ^ 2 + 2 * (P.R ^ 2 + P.δ ^ 2)) := by
  have hj := P.residual_jet_bounds ω u hω
  have hC := C_pos
  have hS := P.S_pos
  have hR := P.R_pos
  have hδ := P.δ_pos
  have hs : (deriv (P.residual ω) u) ^ 2 ≤ (C * P.S * (P.R + P.δ)) ^ 2 := by
    nlinarith [sq_abs (deriv (P.residual ω) u), abs_nonneg (deriv (P.residual ω) u)]
  have hp : |P.residual ω u * deriv (deriv (P.residual ω)) u| ≤
      (C * P.S * (P.R ^ 2 + P.δ ^ 2)) * (2 * C * P.S) := by
    rw [abs_mul]
    exact mul_le_mul hj.1 hj.2.2 (abs_nonneg _) (by positivity)
  have ht := abs_add ((deriv (P.residual ω) u) ^ 2)
    (P.residual ω u * deriv (deriv (P.residual ω)) u)
  rw [abs_of_nonneg (sq_nonneg (deriv (P.residual ω) u))] at ht
  nlinarith

def couplingSize : ℝ := P.μ / P.L * (C ^ 2 * P.S * (P.R + P.δ))

def compensationSize : ℝ := P.μ / P.L ^ 2 *
  (C ^ 2 * P.S ^ 2 * ((P.R + P.δ) ^ 2 + 2 * (P.R ^ 2 + P.δ ^ 2)))

def hessianPerturbation : ℝ := P.couplingSize + P.compensationSize

theorem couplingSize_nonneg : 0 ≤ P.couplingSize := by
  have hμ := P.μ_pos
  have hL := P.L_pos
  have hS := P.S_pos
  have hR := P.R_pos
  have hδ := P.δ_pos
  exact mul_nonneg (div_nonneg hμ.le hL.le) (by positivity)

theorem compensationSize_nonneg : 0 ≤ P.compensationSize := by
  have hμ := P.μ_pos
  unfold compensationSize
  positivity

theorem hessianPerturbation_nonneg : 0 ≤ P.hessianPerturbation :=
  add_nonneg P.couplingSize_nonneg P.compensationSize_nonneg

theorem hessian_entry_bounds (ω : ℝ) (y : LowerSpace) (hω : |ω| ≤ 1) :
    |P.h00 ω y - P.μ| ≤ P.hessianPerturbation ∧
    |P.h01 ω y| ≤ P.hessianPerturbation ∧
    |P.h11 ω y - P.μ| ≤ P.hessianPerturbation := by
  have hc := P.coupling_bounds ω y hω
  have hr := P.compensation_bound ω (y 0) hω
  have hμL : 0 ≤ P.μ / P.L := div_nonneg P.μ_pos.le P.L_pos.le
  have hμL2 : 0 ≤ P.μ / P.L ^ 2 := div_nonneg P.μ_pos.le (sq_nonneg _)
  constructor
  · have ht := abs_add
      (-(P.μ / P.L) * (deriv (deriv (r0 P.S P.R)) (y 0) * normal P.R (y 1) -
        ω * deriv (deriv (r1 P.S P.δ)) (y 0) * normal P.δ (y 1)))
      (P.μ / P.L ^ 2 * ((deriv (P.residual ω) (y 0)) ^ 2 +
        P.residual ω (y 0) * deriv (deriv (P.residual ω)) (y 0)))
    have hb0 := mul_le_mul_of_nonneg_left hc.1 hμL
    have hb1 := mul_le_mul_of_nonneg_left hr hμL2
    rw [abs_mul, abs_neg, abs_of_nonneg hμL, abs_mul, abs_of_nonneg hμL2] at ht
    have he : P.h00 ω y - P.μ =
        -(P.μ / P.L) * (deriv (deriv (r0 P.S P.R)) (y 0) * normal P.R (y 1) -
          ω * deriv (deriv (r1 P.S P.δ)) (y 0) * normal P.δ (y 1)) +
        P.μ / P.L ^ 2 * ((deriv (P.residual ω) (y 0)) ^ 2 +
          P.residual ω (y 0) * deriv (deriv (P.residual ω)) (y 0)) := by unfold h00; ring
    rw [he]
    exact ht.trans (add_le_add hb0 hb1)
  constructor
  · have hb := mul_le_mul_of_nonneg_left hc.2.1 hμL
    have he : |P.h01 ω y| = P.μ / P.L *
        |deriv (r0 P.S P.R) (y 0) * deriv (normal P.R) (y 1) -
          ω * deriv (r1 P.S P.δ) (y 0) * deriv (normal P.δ) (y 1)| := by
      simp only [h01, neg_div, abs_mul, abs_neg, abs_of_nonneg hμL]
    rw [he]
    exact hb.trans (le_add_of_nonneg_right P.compensationSize_nonneg)
  · have hb := mul_le_mul_of_nonneg_left hc.2.2 hμL
    have he : |P.h11 ω y - P.μ| = P.μ / P.L *
        |r0 P.S P.R (y 0) * deriv (deriv (normal P.R)) (y 1) -
          ω * r1 P.S P.δ (y 0) * deriv (deriv (normal P.δ)) (y 1)| := by
      have he' : P.h11 ω y - P.μ = -(P.μ / P.L) *
          (r0 P.S P.R (y 0) * deriv (deriv (normal P.R)) (y 1) -
            ω * r1 P.S P.δ (y 0) * deriv (deriv (normal P.δ)) (y 1)) := by unfold h11; ring
      rw [he', abs_mul, abs_neg, abs_of_nonneg hμL]
    rw [he]
    exact hb.trans (le_add_of_nonneg_right P.compensationSize_nonneg)

/-- The source's perturbation scaling, with an explicit universal numerical factor. -/
theorem hessianPerturbation_scale :
    P.hessianPerturbation ≤ 4 * C ^ 2 * P.μ *
      ((P.S / P.L) * (P.R + P.δ) + (P.S / P.L) ^ 2 * (P.R ^ 2 + P.δ ^ 2)) := by
  have hμ := P.μ_pos
  have hL := P.L_pos
  have hS := P.S_pos
  have hR := P.R_pos
  have hδ := P.δ_pos
  have hcross : (P.R + P.δ) ^ 2 ≤ 2 * (P.R ^ 2 + P.δ ^ 2) := by
    nlinarith [sq_nonneg (P.R - P.δ)]
  have hcomp := mul_le_mul_of_nonneg_left hcross
    (show 0 ≤ P.μ / P.L ^ 2 * C ^ 2 * P.S ^ 2 by positivity)
  have hc : 0 ≤ P.μ / P.L * C ^ 2 * P.S * (P.R + P.δ) := by positivity
  dsimp [hessianPerturbation, couplingSize, compensationSize]
  ring_nf at hcomp hc ⊢
  nlinarith

theorem hessian_coercive (ω : ℝ) (y v : LowerSpace) (hω : |ω| ≤ 1)
    (hsmall : P.hessianPerturbation ≤ P.μ / 4) :
    P.μ / 2 * ‖v‖ ^ 2 ≤ ⟪P.lowerYY ω y v, v⟫ := by
  have he := P.hessian_entry_bounds ω y hω
  have hE := P.hessianPerturbation_nonneg
  have h0 := mul_le_mul_of_nonneg_right (abs_le.mp he.1).1 (sq_nonneg (v 0))
  have h1 := mul_le_mul_of_nonneg_right (abs_le.mp he.2.2).1 (sq_nonneg (v 1))
  have h2 := mul_le_mul_of_nonneg_right P.μ_le_L (sq_nonneg (v 2))
  have hab : 2 * |v 0| * |v 1| ≤ (v 0) ^ 2 + (v 1) ^ 2 := by
    nlinarith [sq_nonneg (|v 0| - |v 1|), sq_abs (v 0), sq_abs (v 1)]
  have hcross : |2 * P.h01 ω y * v 0 * v 1| ≤
      P.hessianPerturbation * ((v 0) ^ 2 + (v 1) ^ 2) := by
    have h := mul_le_mul he.2.1 hab (by positivity) hE
    calc
      _ = |P.h01 ω y| * (2 * |v 0| * |v 1|) := by rw [abs_mul, abs_mul, abs_mul]; norm_num; ring
      _ ≤ _ := h
  have hc := (abs_le.mp hcross).1
  have hs := mul_le_mul_of_nonneg_right hsmall (add_nonneg (sq_nonneg (v 0)) (sq_nonneg (v 1)))
  rw [P.lowerYY_apply, inner_pack, norm_sq]
  nlinarith [mul_nonneg P.μ_pos.le (sq_nonneg (v 2))]

theorem lower_strong_convex (ω : ℝ) (hω : |ω| ≤ 1)
    (hsmall : P.hessianPerturbation ≤ P.μ / 4) (x : ℝ) (u v : LowerSpace) :
    P.lower ω x u + ⟪P.lowerY ω x u, v - u⟫ + (P.μ / 2) / 2 * ‖v - u‖ ^ 2 ≤
      P.lower ω x v :=
  HessianLowerBound.first_order_lower (P.lower_hasGradientY ω x) (P.lowerY_hasFDerivAt ω x)
    (fun y v => P.hessian_coercive ω y v hω hsmall) u v

theorem response_minimizes (ω x : ℝ) (hω : |ω| ≤ 1) (hcore : P.CoreSmallness)
    (hsmall : P.hessianPerturbation ≤ P.μ / 4) (v : LowerSpace) :
    P.lower ω x (P.response ω x) ≤ P.lower ω x v := by
  have h := P.lower_strong_convex ω hω hsmall x (P.response ω x) v
  rw [P.response_stationary ω x hω hcore, inner_zero_left, add_zero] at h
  have hn : 0 ≤ (P.μ / 2) / 2 * ‖v - P.response ω x‖ ^ 2 :=
    mul_nonneg (by linarith [P.μ_pos]) (sq_nonneg _)
  linarith

theorem response_unique (ω x : ℝ) (hω : |ω| ≤ 1) (hcore : P.CoreSmallness)
    (hsmall : P.hessianPerturbation ≤ P.μ / 4) (v : LowerSpace)
    (hv : P.lower ω x v ≤ P.lower ω x (P.response ω x)) : v = P.response ω x := by
  have h := P.lower_strong_convex ω hω hsmall x (P.response ω x) v
  rw [P.response_stationary ω x hω hcore, inner_zero_left, add_zero] at h
  have hn : ‖v - P.response ω x‖ ^ 2 ≤ 0 := by nlinarith [P.μ_pos]
  have hz : ‖v - P.response ω x‖ = 0 := by nlinarith [norm_nonneg (v - P.response ω x)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

/-- A fixed numerical choice of the source's sufficiently small `bar r = S R / L`
simultaneously guarantees the core conditions and global strong convexity. -/
theorem smallness_of_scale (hscale : 4096 * C ^ 2 * P.S * P.R ≤ P.L) :
    P.CoreSmallness ∧ P.hessianPerturbation ≤ P.μ / 4 := by
  have hC := C_one_le
  have hC2 : 1 ≤ C ^ 2 := by nlinarith
  have hS := P.S_pos
  have hR := P.R_pos
  have hδ := P.δ_pos
  have hL := P.L_pos
  have hμ := P.μ_pos
  have hSR : 0 ≤ P.S * P.R := by positivity
  have hCm := mul_le_mul_of_nonneg_right hC2 hSR
  have hfine := mul_le_mul_of_nonneg_left P.delta_le_R P.S_pos.le
  constructor
  · constructor <;> nlinarith
  let θ := P.S / P.L
  let t := θ * P.R
  have hθ : 0 < θ := div_pos hS hL
  have ht : 0 < t := mul_pos hθ hR
  have htScale : 4096 * C ^ 2 * t ≤ 1 := by
    have h := (div_le_one hL).mpr hscale
    convert h using 1
    dsimp [t, θ]
    ring
  have ht1 : t ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right hC2 ht.le
    nlinarith
  have hδθ : θ * P.δ ≤ t := mul_le_mul_of_nonneg_left P.delta_le_R hθ.le
  have hfirst : θ * (P.R + P.δ) ≤ 2 * t := by dsimp [t] at *; nlinarith
  have hsecond : θ ^ 2 * (P.R ^ 2 + P.δ ^ 2) ≤ 2 * t ^ 2 := by
    have hs : P.δ ^ 2 ≤ P.R ^ 2 := by nlinarith [P.delta_le_R]
    have hh := mul_le_mul_of_nonneg_left hs (sq_nonneg θ)
    dsimp [t]
    nlinarith
  have hsum := add_le_add hfirst hsecond
  have hmult := mul_le_mul_of_nonneg_left hsum
    (show 0 ≤ 4 * C ^ 2 * P.μ by positivity)
  have hquad : t ^ 2 ≤ t := by nlinarith
  have hquad' := mul_le_mul_of_nonneg_left hquad
    (show 0 ≤ 8 * C ^ 2 * P.μ by positivity)
  have hlin := mul_le_mul_of_nonneg_left htScale P.μ_pos.le
  have hb := P.hessianPerturbation_scale
  change P.hessianPerturbation ≤ 4 * C ^ 2 * P.μ *
    (θ * (P.R + P.δ) + θ ^ 2 * (P.R ^ 2 + P.δ ^ 2)) at hb
  nlinarith

theorem exact_response (ω x : ℝ) (hω : |ω| ≤ 1)
    (hscale : 4096 * C ^ 2 * P.S * P.R ≤ P.L) :
    (∀ v, P.lower ω x (P.response ω x) ≤ P.lower ω x v) ∧
    (∀ v, P.lower ω x v ≤ P.lower ω x (P.response ω x) → v = P.response ω x) := by
  have hs := P.smallness_of_scale hscale
  exact ⟨P.response_minimizes ω x hω hs.1 hs.2, P.response_unique ω x hω hs.1 hs.2⟩

end Bilevel.SmallGapInstance.Parameters
