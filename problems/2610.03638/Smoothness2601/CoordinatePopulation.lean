import Smoothness2601.CoordinateGeometry

/-! Isometric transport of every source population assumption, its actual
lower minimizer, objective, initialization and complete finite derivative list. -/
noncomputable section
open Bilevel.PrimitiveGeometry
open scoped RealInnerProductSpace
namespace Smoothness2601.CoordinatePopulation
open CoordinateGeometry

variable {X Y Z : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  {b : Budgets} (P : Population (X := X) (Y := Y) b) (e : Z ≃ₗᵢ[ℝ] Y)

set_option maxHeartbeats 2000000 in
def transport : Population (X := X) (Y := Z) b where
  f z := P.f (joint (X := X) e z)
  g z := P.g (joint (X := X) e z)
  grad_f z := (joint (X := X) e).symm (P.grad_f (joint (X := X) e z))
  grad_g z := (joint (X := X) e).symm (P.grad_g (joint (X := X) e z))
  has_f z := gradient_pullback (joint (X := X) e) (P.has_f (joint (X := X) e z))
  has_g z := gradient_pullback (joint (X := X) e) (P.has_g (joint (X := X) e z))
  gyy x y := operator e e.symm (P.gyy x (e y))
  gxy x y := operator e (LinearIsometryEquiv.refl ℝ X) (P.gxy x (e y))
  has_gyy x y := by
    have hh := e.symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp y
      ((P.has_gyy x (e y)).comp y e.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt)
    exact hh
  has_gxy x y := by
    exact (P.has_gxy x (e y)).comp y e.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt
  strong_convex x u v := by
    change P.g (pack x (e u))+
      ⟪e.symm (P.grad_g (pack x (e u))).snd,v-u⟫+b.μ/2*‖v-u‖ ^ 2 ≤ P.g (pack x (e v))
    have he : ⟪e.symm (P.grad_g (pack x (e u))).snd,v-u⟫ =
        ⟪(P.grad_g (pack x (e u))).snd,e v-e u⟫ := by
      rw [← e.map_sub]
      simpa only [e.apply_symm_apply] using
        (e.inner_map_map (e.symm (P.grad_g (pack x (e u))).snd) (v-u)).symm
    rw [he]
    simpa only [← e.map_sub,e.norm_map] using P.strong_convex x (e u) (e v)
  lipschitz_f_y x u v := by
    simpa only [← e.map_sub,e.norm_map] using P.lipschitz_f_y x (e u) (e v)
  smooth_f z w := by
    rw [← map_sub,(joint (X := X) e).symm.norm_map]
    simpa only [← map_sub,(joint (X := X) e).norm_map] using P.smooth_f (joint (X := X) e z) (joint (X := X) e w)
  smooth_g z w := by
    rw [← map_sub,(joint (X := X) e).symm.norm_map]
    simpa only [← map_sub,(joint (X := X) e).norm_map] using P.smooth_g (joint (X := X) e z) (joint (X := X) e w)
  variation_yy x x' y y' := by
    rw [operator_sub]
    apply (operator_norm_le _ _ _).trans
    have hh := P.variation_yy x x' (e y) (e y')
    have he : pack x (e y)-pack x' (e y') = joint (X := X) e (pack x y-pack x' y') := by
      rw [map_sub]
      rfl
    rwa [he,(joint (X := X) e).norm_map] at hh
  variation_xy x x' y y' := by
    rw [operator_sub]
    apply (operator_norm_le _ _ _).trans
    have hh := P.variation_xy x x' (e y) (e y')
    have he : pack x (e y)-pack x' (e y') = joint (X := X) e (pack x y-pack x' y') := by
      rw [map_sub]
      rfl
    rwa [he,(joint (X := X) e).norm_map] at hh

theorem higherRegularity {p : WithTop ℕ} {L : ℕ → ℝ} (hp : P.HigherRegularity p L) :
    (transport P e).HigherRegularity p L := by
  intro q hq hqp x
  obtain ⟨hf,hg,hfb,hgb⟩ := hp q hq hqp x
  have hf' : ContDiff ℝ q ((joint (X := X) e).symm ∘ (fun y => P.grad_f (pack x y)) ∘ e) :=
    (joint (X := X) e).symm.contDiff.comp (hf.comp e.contDiff)
  have hg' : ContDiff ℝ (q+1) ((joint (X := X) e).symm ∘ (fun y => P.grad_g (pack x y)) ∘ e) :=
    (joint (X := X) e).symm.contDiff.comp (hg.comp e.contDiff)
  refine ⟨hf',hg',?_,?_⟩
  · intro u v
    change ‖iteratedFDeriv ℝ q ((joint (X := X) e).symm ∘ (fun y => P.grad_f (pack x y)) ∘ e) u-
      iteratedFDeriv ℝ q ((joint (X := X) e).symm ∘ (fun y => P.grad_f (pack x y)) ∘ e) v‖ ≤ _
    rw [iterated_difference_norm e (joint (X := X) e).symm hf]
    simpa only [← e.map_sub,e.norm_map] using hfb (e u) (e v)
  · intro u v
    change ‖iteratedFDeriv ℝ (q+1) ((joint (X := X) e).symm ∘ (fun y => P.grad_g (pack x y)) ∘ e) u-
      iteratedFDeriv ℝ (q+1) ((joint (X := X) e).symm ∘ (fun y => P.grad_g (pack x y)) ∘ e) v‖ ≤ _
    have hgNat : ContDiff ℝ (q+1:ℕ) (fun y => P.grad_g (pack x y)) := by simpa using hg
    rw [iterated_difference_norm e (joint (X := X) e).symm (q := q+1) hgNat]
    simpa only [← e.map_sub,e.norm_map] using hgb (e u) (e v)

variable [FiniteDimensional ℝ Y] [FiniteDimensional ℝ Z]

theorem yStar (x : X) : (transport P e).yStar x = e.symm (P.yStar x) := by
  apply Eq.symm
  apply (transport P e).yStar_unique x
  intro v
  change P.g (pack x (e (e.symm (P.yStar x)))) ≤ P.g (pack x (e v))
  rw [e.apply_symm_apply]
  exact P.yStar_minimizes x (e v)

theorem objective : (transport P e).objective = P.objective := by
  funext x
  unfold Population.objective
  rw [yStar]
  change P.f (pack x (e (e.symm (P.yStar x)))) = P.f (pack x (P.yStar x))
  rw [e.apply_symm_apply]

theorem initialized {x₀ : X} {y₀ : Y} (hi : P.Initialized x₀ y₀) :
    (transport P e).Initialized x₀ (e.symm y₀) := by
  refine ⟨?_,?_,?_⟩
  · simpa only [objective] using hi.bounded_below
  · simpa only [objective] using hi.initial_gap
  · rw [yStar,← map_sub,e.symm.norm_map]
    exact hi.inner_error

end Smoothness2601.CoordinatePopulation
