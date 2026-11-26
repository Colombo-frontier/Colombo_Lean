import Smoothness2601.SineResponse

/-! Actual amplitude/spatial scaling of the split potential and its verified
profile bounds. -/
noncomputable section
open Bilevel.PrimitiveGeometry
open scoped RealInnerProductSpace
namespace Smoothness2601.SineGeometry
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

omit [CompleteSpace X] in
theorem scaled_vector_lipschitz (g : X → X) {L c scale : ℝ}
    (hL : ∀ x z, ‖g x-g z‖ ≤ L*‖x-z‖) (hc : 0 ≤ c) (hs : 0 < scale) (x z : X) :
    ‖c • g (scale⁻¹ • x)-c • g (scale⁻¹ • z)‖ ≤ (c*L/scale)*‖x-z‖ := by
  rw [← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_nonneg hc]
  have hh := mul_le_mul_of_nonneg_left (hL (scale⁻¹ • x) (scale⁻¹ • z)) hc
  rw [← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hs)] at hh
  exact hh.trans_eq (by ring)

namespace Profiles
variable (F : Profiles X)

def scaled {amp scale : ℝ} (ha : 0 ≤ amp) (hs : 0 < scale) : Profiles X where
  A := fun x => amp*F.A (scale⁻¹ • x)
  B := fun x => F.B (scale⁻¹ • x)
  gA := fun x => (amp/scale) • F.gA (scale⁻¹ • x)
  gB := fun x => scale⁻¹ • F.gB (scale⁻¹ • x)
  LA := amp*F.LA/scale^2
  C₀ := F.C₀
  C₁ := F.C₁/scale
  C₂ := F.C₂/scale^2
  LA_nonneg := by have := F.LA_nonneg; positivity
  C₀_nonneg := F.C₀_nonneg
  C₁_nonneg := by have := F.C₁_nonneg; positivity
  C₂_nonneg := by have := F.C₂_nonneg; positivity
  has_A := by
    intro x
    apply hasGradientAt_iff_hasFDerivAt.mpr
    have hd := (SineLift.scaled_hasGradientAt F.A F.gA F.has_A scale x).hasFDerivAt.const_mul amp
    convert hd using 1
    ext v
    simp [InnerProductSpace.toDual_apply,real_inner_smul_left,div_eq_mul_inv]
    ring
  has_B := SineLift.scaled_hasGradientAt F.B F.gB F.has_B scale
  bound_B := fun x => F.bound_B _
  bound_gB := by
    intro x
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hs)]
    exact (mul_le_mul_of_nonneg_left (F.bound_gB _) (inv_nonneg.mpr hs.le)).trans_eq (by ring)
  lip_gA := by
    intro x z
    exact (scaled_vector_lipschitz F.gA F.lip_gA (div_nonneg ha hs.le) hs x z).trans_eq (by ring)
  lip_gB := by
    intro x z
    exact (scaled_vector_lipschitz F.gB F.lip_gB (inv_nonneg.mpr hs.le) hs x z).trans_eq (by ring)

end Profiles
end Smoothness2601.SineGeometry
