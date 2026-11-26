import Smoothness2601.WrappedProfiles
import Smoothness2601.ScaledProfiles

/-! Actual decoupled quadratic-inner populations for the boundary lower bound.
Their upper objective is the same wrapped zero chain. -/
noncomputable section
open Bilevel.PrimitiveGeometry
namespace Smoothness2601.SineGeometry.Profiles
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  (F : Profiles X)

def sumAsUpper : Profiles X where
  A := fun x => F.A x+F.B x
  B := fun _ => 0
  gA := fun x => F.gA x+F.gB x
  gB := fun _ => 0
  LA := F.LA+F.C₂
  C₀ := 0
  C₁ := 0
  C₂ := 0
  LA_nonneg := add_nonneg F.LA_nonneg F.C₂_nonneg
  C₀_nonneg := le_rfl
  C₁_nonneg := le_rfl
  C₂_nonneg := le_rfl
  has_A := fun x => hasGradientAt_iff_hasFDerivAt.mpr (by
    simpa only [map_add] using (F.has_A x).hasFDerivAt.add (F.has_B x).hasFDerivAt)
  has_B := fun _ => by
    apply hasGradientAt_iff_hasFDerivAt.mpr
    simpa using hasFDerivAt_const (0:ℝ) _
  bound_B := fun _ => by simp
  bound_gB := fun _ => by simp
  lip_gA := by
    intro x z
    rw [show F.gA x+F.gB x-(F.gA z+F.gB z) = (F.gA x-F.gA z)+(F.gB x-F.gB z) by abel]
    exact (norm_add_le _ _).trans ((add_le_add (F.lip_gA x z) (F.lip_gB x z)).trans_eq (by ring))
  lip_gB := fun _ _ => by simp

end Smoothness2601.SineGeometry.Profiles

namespace Smoothness2601.BoundaryInstance
open SineGeometry ExtensiveChain HardProfiles
variable (b : Budgets)

def spatialConstant : ℝ := b.μ/(upperSmoothness+frontierSmoothness+1)

theorem spatialConstant_pos : 0 < spatialConstant b :=
  div_pos b.μ_pos (by linarith [upperSmoothness_nonneg,frontierSmoothness_nonneg])

theorem spatialConstant_smooth : spatialConstant b*(upperSmoothness+frontierSmoothness) ≤ b.μ := by
  have hp : 0 < upperSmoothness+frontierSmoothness+1 := by
    linarith [upperSmoothness_nonneg,frontierSmoothness_nonneg]
  unfold spatialConstant
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hp).mpr
  nlinarith [b.μ_pos]

variable {b} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {n : ℕ} (U : Space n →ₗᵢ[ℝ] E) {s : ℝ} (hs : 0 < s)

def profiles : Profiles E :=
  (HardProfiles.profiles U).sumAsUpper.scaled
    (amp := s^2/spatialConstant b) (scale := s/spatialConstant b)
    (by have := spatialConstant_pos b; positivity) (by have := spatialConstant_pos b; positivity)

def calibration (hμL : b.μ ≤ b.L₁) : (profiles (b := b) U hs).Calibration b where
  m := b.μ
  a := 0
  h := 1
  c := 0
  m_nonneg := b.μ_pos.le
  a_nonneg := le_rfl
  h_pos := zero_lt_one
  upper_y := by simpa using b.L₀_pos.le
  upper_smooth := by
    change (s^2/spatialConstant b)*(upperSmoothness+frontierSmoothness)/(s/spatialConstant b)^2 ≤ b.L₁
    have he : (s^2/spatialConstant b)*(upperSmoothness+frontierSmoothness)/(s/spatialConstant b)^2 =
        spatialConstant b*(upperSmoothness+frontierSmoothness) := by
      have := (spatialConstant_pos b).ne'
      field_simp
      ring
    rw [he]
    exact (spatialConstant_smooth b).trans hμL
  strong := by simp
  lower_smooth := by simpa [Profiles.signalLipschitz] using hμL
  mixed_lipschitz := by simpa using b.L₂_pos.le
  lower_lipschitz := by simpa using b.L₂_pos.le

def population (hμL : b.μ ≤ b.L₁) : Population (X := E) (Y := ℝ) b :=
  (profiles U hs).population (calibration U hs hμL)

theorem zero_inner (hμL : b.μ ≤ b.L₁) (x : E) : (population U hs hμL).yStar x = 0 := by
  exact (profiles U hs).population_zero_inner (calibration U hs hμL) x rfl

theorem higherRegularity (hμL : b.μ ≤ b.L₁) (p : WithTop ℕ) (L : ℕ → ℝ)
    (hL : ∀ j, 0 ≤ L j) : (population U hs hμL).HigherRegularity p L := by
  apply (profiles U hs).population_higherRegularity (calibration U hs hμL) p L hL
  intro k _ _
  change b.μ*0*_*_ ≤ L (k+1)
  simpa using hL (k+1)

theorem objective_gradient (hμL : b.μ ≤ b.L₁) (x : E) :
    gradient (population U hs hμL).objective x =
      s • ((HardProfiles.profiles U).gA ((s/spatialConstant b)⁻¹ • x)+
        (HardProfiles.profiles U).gB ((s/spatialConstant b)⁻¹ • x)) := by
  unfold population
  rw [(profiles U hs).population_objective_gradient (calibration U hs hμL)]
  simp only [show (calibration U hs hμL).c = 0 from rfl,zero_mul,zero_smul,add_zero]
  change ((s^2/spatialConstant b)/(s/spatialConstant b)) •
    ((HardProfiles.profiles U).gA ((s/spatialConstant b)⁻¹ • x)+
      (HardProfiles.profiles U).gB ((s/spatialConstant b)⁻¹ • x)) = _
  congr 1
  have := (spatialConstant_pos b).ne'
  field_simp
  ring

end Smoothness2601.BoundaryInstance
