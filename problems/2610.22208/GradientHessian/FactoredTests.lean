import GradientHessian.FreshMarkTests
import GradientHessian.MemoryHitProbability
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

/-! Independent finite-list bounds pulled back to the original raw law by
an explicit measure-preserving equivalence. The list is a function of the
external-data factor only; constructing that list from a censored policy is
a separate obligation. -/

noncomputable section
namespace GradientHessian.FactoredTests
open MeasureTheory
open scoped InnerProductSpace

variable {Ω Θ W : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ] [MeasurableSpace W]

theorem list_bound (e : Ω ≃ᵐ Θ × W) (ρ : Measure Ω) (ν : Measure Θ) (μ : Measure W)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure μ] (he : MeasurePreserving e ρ (ν.prod μ))
    (N : ℕ) (hit : Fin N → W → Θ → Prop)
    (hmeas : ∀ i, MeasurableSet {z : W × Θ | hit i z.1 z.2})
    {p : ℝ} (hp : 0≤p) (hpoint : ∀ i, ∀ᵐ w ∂μ, ν.real {θ | hit i w θ}≤p) :
    ρ.real {x | ∃ i, hit i (e x).2 (e x).1} ≤ N*p := by
  have hs : MeasurableSet {z : W × Θ | ∃ i, hit i z.1 z.2} := by
    convert MeasurableSet.iUnion hmeas using 1
    ext z
    simp
  have hswap : MeasurePreserving (fun x => ((e x).2,(e x).1)) ρ (μ.prod ν) :=
    Measure.measurePreserving_swap.comp he
  have hb := FreshMarkTests.independent_list_bound μ ν N hit hmeas hp hpoint
  change ρ.real ((fun x => ((e x).2,(e x).1)) ⁻¹' {z : W × Θ | ∃ i, hit i z.1 z.2}) ≤ N*p
  rw [hswap.measureReal_preimage hs.nullMeasurableSet]
  exact hb

theorem memory_list_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
    (e : Ω ≃ᵐ E × W) (ρ : Measure Ω) (μ : Measure W) [IsProbabilityMeasure μ]
    (he : MeasurePreserving e ρ ((SphereGaussian.sphereLaw E).prod μ))
    (N : ℕ) (r : ℝ) (queries : W → Fin N → E) (hq : ∀ i, Measurable (fun w => queries w i)) :
    ρ.real {x | ∃ i, (1/8:ℝ) < |LatchChain.u r (e x).1 (queries (e x).2 i)|} ≤
      N*(2*Real.exp (-(Module.finrank ℝ E:ℝ)/18432)) := by
  apply list_bound e ρ (SphereGaussian.sphereLaw E) μ he N
    (fun i w v => (1/8:ℝ) < |LatchChain.u r v (queries w i)|)
  · intro i
    apply measurableSet_lt measurable_const
    apply Measurable.abs
    exact measurable_snd.inner
      ((RadialSquash.squash_contDiff (by norm_num : (0:ℝ)<8)).continuous.measurable.comp
        (measurable_const.smul ((hq i).comp measurable_fst)))
  · positivity
  · intro i
    exact Filter.Eventually.of_forall (fun w => MemoryHitProbability.repair_hit_bound r (queries w i))

end GradientHessian.FactoredTests
