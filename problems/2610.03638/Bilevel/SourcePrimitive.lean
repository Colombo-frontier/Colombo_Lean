import Bilevel.PrimitiveGeometry

/-! Source-facing full Euclidean gradient assumptions and their exact
conversion to the block primitive used by the formalized proofs. -/
noncomputable section
open scoped RealInnerProductSpace

namespace Bilevel.PrimitiveGeometry
variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

structure FullPrimitive (μ Lf Lg Cf ρ : ℝ) where
  μ_pos : 0 < μ
  Lf_nonneg : 0 ≤ Lf
  Lg_nonneg : 0 ≤ Lg
  Cf_nonneg : 0 ≤ Cf
  ρ_nonneg : 0 ≤ ρ
  f : Joint X Y → ℝ
  g : Joint X Y → ℝ
  grad_f : Joint X Y → Joint X Y
  grad_g : Joint X Y → Joint X Y
  has_f : ∀ z, HasGradientAt f (grad_f z) z
  has_g : ∀ z, HasGradientAt g (grad_g z) z
  gyy : X → Y → (Y →L[ℝ] Y)
  gxy : X → Y → (Y →L[ℝ] X)
  has_gyy : ∀ x y, HasFDerivAt (fun v => (grad_g (pack x v)).snd) (gyy x y) y
  has_gxy : ∀ x y, HasFDerivAt (fun v => (grad_g (pack x v)).fst) (gxy x y) y
  strong_convex : ∀ x u v, g (pack x u) + ⟪(grad_g (pack x u)).snd,v-u⟫ +
    μ/2*‖v-u‖^2 ≤ g (pack x v)
  upper_bound : ∀ z, ‖(grad_f z).snd‖ ≤ Cf
  smooth_f : ∀ z w, ‖grad_f z-grad_f w‖ ≤ Lf*‖z-w‖
  smooth_g : ∀ z w, ‖grad_g z-grad_g w‖ ≤ Lg*‖z-w‖
  variation_yy : ∀ x x' y y', ‖gyy x y-gyy x' y'‖ ≤ ρ*‖pack x y-pack x' y'‖
  variation_xy : ∀ x x' y y', ‖gxy x y-gxy x' y'‖ ≤ ρ*‖pack x y-pack x' y'‖

def FullPrimitive.toPrimitive {μ Lf Lg Cf ρ : ℝ}
    (P : FullPrimitive (X := X) (Y := Y) μ Lf Lg Cf ρ) :
    Model.Primitive (X := X) (Y := Y) μ Lf Lg Cf ρ where
  μ_pos := P.μ_pos
  Lf_nonneg := P.Lf_nonneg
  Lg_nonneg := P.Lg_nonneg
  Cf_nonneg := P.Cf_nonneg
  ρ_nonneg := P.ρ_nonneg
  f x y := P.f (pack x y)
  g x y := P.g (pack x y)
  fx x y := (P.grad_f (pack x y)).fst
  fy x y := (P.grad_f (pack x y)).snd
  gx x y := (P.grad_g (pack x y)).fst
  gy x y := (P.grad_g (pack x y)).snd
  gyy := P.gyy
  gxy := P.gxy
  has_fx x y := partial_x (P.has_f (pack x y))
  has_fy x y := partial_y (P.has_f (pack x y))
  has_gx x y := partial_x (P.has_g (pack x y))
  has_gy x y := partial_y (P.has_g (pack x y))
  has_gyy := P.has_gyy
  has_gxy := P.has_gxy
  strong_convex := P.strong_convex
  upper_bound x y := P.upper_bound (pack x y)
  smooth_f := (full_gradient_lipschitz_iff _ _ P.Lf_nonneg).mp
    (fun x x' y y' => P.smooth_f (pack x y) (pack x' y'))
  smooth_g := (full_gradient_lipschitz_iff _ _ P.Lg_nonneg).mp
    (fun x x' y y' => P.smooth_g (pack x y) (pack x' y'))
  variation_yy x x' y y' := by simpa only [norm_sub_pack] using P.variation_yy x x' y y'
  variation_xy x x' y y' := by simpa only [norm_sub_pack] using P.variation_xy x x' y y'

end Bilevel.PrimitiveGeometry

namespace Bilevel.Model.Primitive
variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  {μ Lf Lg Cf ρ Δ : ℝ} (P : Primitive (X := X) (Y := Y) μ Lf Lg Cf ρ)
  (r : P.Response) (x0 : X)

theorem gapCertificate_iff_source :
    Nonempty (P.GapCertificate r x0 Δ) ↔
      BddBelow (Set.range (P.hyperobjective r)) ∧
        P.hyperobjective r x0 - sInf (Set.range (P.hyperobjective r)) ≤ Δ := by
  constructor
  · rintro ⟨G⟩
    have hb : BddBelow (Set.range (P.hyperobjective r)) :=
      ⟨G.floor, by rintro _ ⟨x,rfl⟩; exact G.lower_bound x⟩
    refine ⟨hb, ?_⟩
    have hlo : G.floor ≤ sInf (Set.range (P.hyperobjective r)) := by
      apply le_csInf (Set.range_nonempty _)
      rintro _ ⟨x,rfl⟩
      exact G.lower_bound x
    linarith [G.gap]
  · rintro ⟨hb,hgap⟩
    exact ⟨⟨sInf (Set.range (P.hyperobjective r)),
      fun x => csInf_le hb (Set.mem_range_self x), hgap⟩⟩

end Bilevel.Model.Primitive
