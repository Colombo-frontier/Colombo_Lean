import Bilevel.SmallGapVariation
import Bilevel.SmallGapRealizedObjective

/-!
The actual fixed-dimensional small-gap family as a complete `Model.Primitive`.
The numerical scale condition fixes the source's sufficiently small universal
coarse radius. Every derivative, global regularity budget, and minimizer fact
used in this instance is proved from the displayed clipped objectives.
-/

noncomputable section
namespace Bilevel.SmallGapInstance.Parameters

open SmallGapLiftSupport

variable (P : Parameters)

def primitive (ω : ℝ) (hω : |ω| ≤ 1)
    (hscale : 4096 * C ^ 2 * P.S * P.R ≤ P.L) :
    Model.Primitive (X := ℝ) (Y := LowerSpace) (P.μ / 2) P.L (3 * P.L) P.L P.rawRho where
  μ_pos := div_pos P.μ_pos (by norm_num)
  Lf_nonneg := P.L_pos.le
  Lg_nonneg := mul_nonneg (by norm_num) P.L_pos.le
  Cf_nonneg := P.L_pos.le
  ρ_nonneg := P.rawRho_nonneg
  f := P.upper
  g := P.lower ω
  fx := P.upperX
  fy := P.upperY
  gx := P.lowerX ω
  gy := P.lowerY ω
  gyy := fun _ => P.lowerYY ω
  gxy := fun _ _ => P.lowerXY
  has_fx := P.upper_hasGradientX
  has_fy := P.upper_hasGradientY
  has_gx := P.lower_hasGradientX ω
  has_gy := P.lower_hasGradientY ω
  has_gyy := P.lowerY_hasFDerivAt ω
  has_gxy := P.lowerX_hasFDerivAt ω
  strong_convex := P.lower_strong_convex ω hω (P.smallness_of_scale hscale).2
  upper_bound := fun x y => (P.upperY_norm x y).le
  smooth_f := P.upper_smooth
  smooth_g := P.lower_smooth ω hω (P.smallness_of_scale hscale).2
  variation_yy := P.hessian_variation_joint ω hω hscale
  variation_xy := by
    intro x x' y y'
    simp only [sub_self, norm_zero]
    exact mul_nonneg P.rawRho_nonneg (Real.sqrt_nonneg _)

def responseCertificate (ω : ℝ) (hω : |ω| ≤ 1)
    (hscale : 4096 * C ^ 2 * P.S * P.R ≤ P.L) : (P.primitive ω hω hscale).Response where
  y := P.response ω
  minimizes x := P.response_minimizes ω x hω
    (P.smallness_of_scale hscale).1 (P.smallness_of_scale hscale).2

theorem primitive_hyperobjective_eq (ω : ℝ) (hω : |ω| ≤ 1)
    (hscale : 4096 * C ^ 2 * P.S * P.R ≤ P.L) :
    (P.primitive ω hω hscale).hyperobjective (P.responseCertificate ω hω hscale) =
      P.realizedObjective ω := rfl

theorem primitive_initial_response (ω : ℝ) (hω : |ω| ≤ 1)
    (hscale : 4096 * C ^ 2 * P.S * P.R ≤ P.L) :
    (P.responseCertificate ω hω hscale).y 0 = 0 := P.response_zero ω

theorem primitive_hypergradient_separation (hgeometry : P.Geometry)
    (hscale : 4096 * C ^ 2 * P.S * P.R ≤ P.L) (x : ℝ) :
    2 * ((P.L / P.μ) * P.S * P.δ) ≤
      |deriv ((P.primitive 1 (by norm_num) hscale).hyperobjective
        (P.responseCertificate 1 (by norm_num) hscale)) x| +
      |deriv ((P.primitive (-1) (by norm_num) hscale).hyperobjective
        (P.responseCertificate (-1) (by norm_num) hscale)) x| :=
  P.realizedObjective_separation hgeometry x

def gapCertificate (ω : ℝ) (hω : |ω| ≤ 1) (hsign : ω = 1 ∨ ω = -1)
    (hgeometry : P.Geometry) (hscale : 4096 * C ^ 2 * P.S * P.R ≤ P.L) :
    (P.primitive ω hω hscale).GapCertificate (P.responseCertificate ω hω hscale) 0
      (((P.L / P.μ) * P.S * P.δ) ^ 2 / (2 * ((P.L / P.μ) ^ 2 * P.S))) := by
  let xstar := Classical.choose (P.realizedObjective_minimum_exists hgeometry ω)
  have hmin : ∀ x, P.realizedObjective ω xstar ≤ P.realizedObjective ω x :=
    Classical.choose_spec (P.realizedObjective_minimum_exists hgeometry ω)
  exact {
    floor := P.realizedObjective ω xstar
    lower_bound := hmin
    gap := (P.realizedObjective_gap hgeometry ω xstar hsign hmin).2
  }

end Bilevel.SmallGapInstance.Parameters
