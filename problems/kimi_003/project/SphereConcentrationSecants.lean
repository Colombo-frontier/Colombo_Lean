import SphereConcentration
import HaarRebalancingRootMoment

/-!
Connect the actual two-value same-sample central secant formula to the proved
spherical-analysis inputs. Sample functions are required to be Lipschitz only
on the legal query domain. No stochastic concentration or directional moment
conclusion is a premise.
-/

open Set MeasureTheory ProbabilityTheory Real Metric
open scoped ENNReal NNReal

namespace Task006.SphereConcentration
noncomputable section

/-- A common sample and common smoothing center are used by both evaluations. -/
def sampledCentralSecant {Sample E : Type*} [AddCommGroup E] [Module ℝ E]
    (F : Sample → E → ℝ) (center : Sample → E) (δ : ℝ) (z : Sample) (q : E) : ℝ :=
  centralSecant (F z) (center z) δ q

/-- Jointly measurable sample values and centers give the actual joint
measurability of the symmetric secant family. -/
theorem sampledCentralSecant_measurable {d : ℕ} {Sample : Type*} [MeasurableSpace Sample]
    {F : Sample → EuclideanSpace ℝ (Fin d) → ℝ}
    {center : Sample → EuclideanSpace ℝ (Fin d)} (δ : ℝ)
    (hF : Measurable (fun p : Sample × EuclideanSpace ℝ (Fin d) => F p.1 p.2))
    (hc : Measurable center) :
    Measurable (fun p : Sample × EuclideanSpace ℝ (Fin d) =>
      sampledCentralSecant F center δ p.1 p.2) := by
  have hp : Measurable (fun p : Sample × EuclideanSpace ℝ (Fin d) => center p.1 + δ • p.2) :=
    (hc.comp measurable_fst).add ((measurable_const : Measurable (fun _ : Sample × EuclideanSpace ℝ (Fin d) => δ)).smul measurable_snd)
  have hm : Measurable (fun p : Sample × EuclideanSpace ℝ (Fin d) => center p.1 - δ • p.2) :=
    (hc.comp measurable_fst).sub ((measurable_const : Measurable (fun _ : Sample × EuclideanSpace ℝ (Fin d) => δ)).smul measurable_snd)
  exact ((hF.comp (measurable_fst.prodMk hp)).sub
    (hF.comp (measurable_fst.prodMk hm))).div_const (2 * δ)

theorem sampledCentralSecant_odd {Sample E : Type*} [AddCommGroup E] [Module ℝ E]
    (F : Sample → E → ℝ) (center : Sample → E) (δ : ℝ) (z : Sample) (q : E) :
    sampledCentralSecant F center δ z (-q) = -sampledCentralSecant F center δ z q :=
  centralSecant_odd (F z) (center z) δ q

/-- Legal-domain sample Lipschitzness implies the actual sphere-secant
Lipschitz estimate. No extension of sample Lipschitzness outside that domain
is assumed. -/
theorem sampledCentralSecant_lipschitz {d : ℕ} {Sample : Type*}
    {F : Sample → EuclideanSpace ℝ (Fin d) → ℝ}
    {center : Sample → EuclideanSpace ℝ (Fin d)} {δ : ℝ}
    {S : Set (EuclideanSpace ℝ (Fin d))} (G : Sample → ℝ≥0) (hδ : 0 < δ)
    (hF : ∀ z, ∀ x ∈ S, ∀ y ∈ S, |F z x - F z y| ≤ (G z : ℝ) * ‖x - y‖)
    (hlegal : ∀ z q, ‖q‖ = 1 → center z + δ • q ∈ S ∧ center z - δ • q ∈ S) :
    ∀ z, LipschitzOnWith (G z) (sampledCentralSecant F center δ z) (sphere (0 : _) 1) := by
  intro z
  apply LipschitzOnWith.of_dist_le_mul
  intro q hq q' hq'
  have hqn : ‖q‖ = 1 := mem_sphere_zero_iff_norm.mp hq
  have hq'n : ‖q'‖ = 1 := mem_sphere_zero_iff_norm.mp hq'
  have h := centralSecant_lipschitz hδ (hF z) (center z) q q'
    (hlegal z q hqn).1 (hlegal z q hqn).2 (hlegal z q' hq'n).1 (hlegal z q' hq'n).2
  simpa only [sampledCentralSecant, Real.dist_eq, dist_eq_norm, Real.norm_eq_abs] using h

/-- The actual secant is bounded by G on every legal unit direction. -/
theorem sampledCentralSecant_abs_le {d : ℕ} {Sample : Type*}
    {F : Sample → EuclideanSpace ℝ (Fin d) → ℝ}
    {center : Sample → EuclideanSpace ℝ (Fin d)} {δ : ℝ}
    {S : Set (EuclideanSpace ℝ (Fin d))} (G : Sample → ℝ≥0) (hδ : 0 < δ)
    (hF : ∀ z, ∀ x ∈ S, ∀ y ∈ S, |F z x - F z y| ≤ (G z : ℝ) * ‖x - y‖)
    (hlegal : ∀ z q, ‖q‖ = 1 → center z + δ • q ∈ S ∧ center z - δ • q ∈ S) :
    ∀ z q, ‖q‖ = 1 → |sampledCentralSecant F center δ z q| ≤ G z := by
  intro z q hq
  exact abs_centralSecant_le (G z).coe_nonneg hδ (hF z) (center z) q hq.le
    (hlegal z q hq).1 (hlegal z q hq).2

end
end Task006.SphereConcentration
