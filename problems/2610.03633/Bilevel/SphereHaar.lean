import Bilevel.OrthogonalAction
import Bilevel.InvariantAdaptation

/-! Haar orbits on the unit sphere have the actual normalized Gaussian law. -/
noncomputable section
open MeasureTheory
open scoped ENNReal RealInnerProductSpace
namespace Bilevel.SphereHaar
open EuclideanGaussian OrthogonalAction
set_option synthInstance.maxHeartbeats 100000

theorem orbit_average_eq (d : ℕ) (f : Space d → ℝ≥0∞) (x y : Space d)
    (hxy : ‖x‖ = ‖y‖) :
    (∫⁻ A, f (A • y) ∂OrthogonalHaar.law d) =
      ∫⁻ A, f (A • x) ∂OrthogonalHaar.law d := by
  obtain ⟨B, rfl⟩ := transitive_on_sphere d x y hxy
  simp_rw [← mul_smul]
  exact lintegral_mul_right_eq_self (fun A : OrthogonalHaar.Group d => f (A • x)) B

theorem orbit_lintegral (n : ℕ) (f : Space (n + 1) → ℝ≥0∞) (hf : Measurable f)
    (x : Space (n + 1)) (hx : ‖x‖ = 1) :
    (∫⁻ A, f (A • x) ∂OrthogonalHaar.law (n + 1)) =
      ∫⁻ y, f y ∂SphereLaw.sphereLaw (n + 1) := by
  calc
    (∫⁻ A, f (A • x) ∂OrthogonalHaar.law (n + 1)) =
        ∫⁻ y, ∫⁻ A, f (A • y) ∂OrthogonalHaar.law (n + 1) ∂SphereLaw.sphereLaw (n + 1) := by
      calc
        _ = ∫⁻ _y, (∫⁻ A, f (A • x) ∂OrthogonalHaar.law (n + 1)) ∂SphereLaw.sphereLaw (n + 1) := by simp
        _ = _ := by
          apply lintegral_congr_ae
          filter_upwards [SphereLaw.unit_norm_ae n] with y hy
          exact (orbit_average_eq (n + 1) f x y (hx.trans hy.symm)).symm
    _ = ∫⁻ A, ∫⁻ y, f (A • y) ∂SphereLaw.sphereLaw (n + 1) ∂OrthogonalHaar.law (n + 1) := by
      apply lintegral_lintegral_swap
      exact (hf.comp (measurable_snd.smul measurable_fst)).aemeasurable
    _ = ∫⁻ y, f y ∂SphereLaw.sphereLaw (n + 1) :=
      InvariantAdaptation.lintegral_action_average _ _ (sphere_preserving (n + 1)) f hf

theorem orbit_preserving (n : ℕ) (x : Space (n + 1)) (hx : ‖x‖ = 1) :
    MeasurePreserving (fun A : OrthogonalHaar.Group (n + 1) => A • x)
      (OrthogonalHaar.law (n + 1)) (SphereLaw.sphereLaw (n + 1)) := by
  refine ⟨measurable_id.smul measurable_const, ?_⟩
  apply (Measure.ext_iff_lintegral _).mpr
  intro f hf
  have hm : Measurable (fun A : OrthogonalHaar.Group (n + 1) => A • x) :=
    measurable_id.smul measurable_const
  rw [lintegral_map hf hm]
  exact orbit_lintegral n f hf x hx

theorem haar_directional_tail (n : ℕ) (t : ℝ) (ht : 0 < t) (ht2 : t ≤ 2)
    (w x : Space (n + 1)) (hw : ‖w‖ = 1) (hx : ‖x‖ = 1) :
    (OrthogonalHaar.law (n + 1)).real {A | t ≤ ⟪w, (A • x : Space (n + 1))⟫ ^ 2} ≤
      2 * Real.exp (-(n : ℝ) * t / 8) := by
  have hs : MeasurableSet {y : Space (n + 1) | t ≤ ⟪w, y⟫ ^ 2} :=
    measurableSet_le measurable_const ((continuous_const.inner continuous_id).measurable.pow_const 2)
  rw [show {A : OrthogonalHaar.Group (n + 1) | t ≤ ⟪w, A • x⟫ ^ 2} =
      (fun A : OrthogonalHaar.Group (n + 1) => A • x) ⁻¹' {y | t ≤ ⟪w, y⟫ ^ 2} from rfl,
    SphericalGaussian.measureReal_preimage (orbit_preserving n x hx) _ hs]
  exact SphereLaw.directional_tail n t ht ht2 w hw

end Bilevel.SphereHaar
