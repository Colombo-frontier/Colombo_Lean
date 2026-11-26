import Smoothness2601.SineRegularity
import Smoothness2601.SineHypergradient

/-! Identify the constructed root with the actual Population minimizer. -/
noncomputable section
open Bilevel.PrimitiveGeometry
namespace Smoothness2601.SineGeometry.Profiles
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  (F : Profiles X) {b : Budgets} (S : F.Calibration b)

theorem calibrated_m_pos : 0 < S.m := by
  by_contra h
  have hz : S.m = 0 := le_antisymm (le_of_not_gt h) S.m_nonneg
  have hs := S.strong
  rw [hz,zero_mul] at hs
  exact (not_le.mpr b.μ_pos) hs

theorem calibrated_small : (S.a/S.h)*F.C₀ < 1 := by
  have hs := S.strong
  have hm := F.calibrated_m_pos S
  nlinarith [b.μ_pos]

theorem calibrated_point_small (x : X) : |(S.a/S.h)*F.B x| < 1 := by
  rw [abs_mul,abs_of_nonneg (div_nonneg S.a_nonneg S.h_pos.le)]
  exact (mul_le_mul_of_nonneg_left (F.bound_B x) (div_nonneg S.a_nonneg S.h_pos.le)).trans_lt
    (F.calibrated_small S)

theorem population_yStar (x : X) :
    (F.population S).yStar x = SineLift.lowerRoot S.a S.h (F.B x) := by
  apply Eq.symm
  apply (F.population S).yStar_unique x
  exact (SineLift.lowerRoot_unique_minimizer (F.calibrated_m_pos S) S.h_pos.ne'
    (F.calibrated_point_small S x)).1

theorem population_zero_inner (x : X) (hx : F.B x = 0) : (F.population S).yStar x = 0 := by
  rw [F.population_yStar S x,hx,SineLift.lowerRoot_zero]

theorem population_objective : (F.population S).objective =
    fun x => F.A x+S.c*S.a*SineLift.theta (S.a/S.h) (F.B x) := by
  funext x
  change upper F.A S.c (pack x ((F.population S).yStar x)) = _
  rw [F.population_yStar S x]
  change F.A x+S.c*(S.a*SineLift.theta (S.a/S.h) (F.B x)) = _
  ring

theorem population_objective_gradient (x : X) :
    gradient (F.population S).objective x =
      F.gA x+(S.c*S.a*deriv (SineLift.theta (S.a/S.h)) (F.B x)) • F.gB x := by
  rw [F.population_objective S]
  have hb := SineLift.theta_comp_hasGradientAt F.B F.gB F.has_B x (F.calibrated_point_small S x)
  apply HasGradientAt.gradient
  apply hasGradientAt_iff_hasFDerivAt.mpr
  have hd := (F.has_A x).hasFDerivAt.add (hb.hasFDerivAt.const_mul (S.c*S.a))
  convert hd using 1
  ext v
  simp [InnerProductSpace.toDual_apply,inner_add_left,real_inner_smul_left]
  ring

end Smoothness2601.SineGeometry.Profiles
