import Nonsmooth.GaussianSpectral
import Nonsmooth.ConditionalLower
import Nonsmooth.GaussianSingleHardness

open MeasureTheory
open scoped ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

/-- The sole remaining probabilistic assertion about the now fully specified
Gaussian support prior. This is an explicit hypothesis, not an established theorem. -/
def GaussianAdaptiveHardnessInput (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
    (cprob : ℝ) : Prop :=
  ∀ (k : ℕ) (hk : 0 < k),
    letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    256 ≤ Module.finrank ℝ E → (k : ℝ) ≤ (Module.finrank ℝ E : ℝ) / 512 →
    ∀ T : ℕ, (T : ℝ) ≤ cprob * Module.finrank ℝ E * k / Real.log (Real.exp 1 * k) →
    ∀ (S : Type) (mS : MeasurableSpace S), letI := mS
      ∀ q : Policy Unit S (Feasible E 1), q.IsMeasurable →
        3 / 4 ≤ (gaussianSupportPrior E k).real {a : BoundedSupportRows E (Fin k) |
          7 * ((1 / 4 : ℝ) / Real.sqrt k) / 16 <
            boundedFiniteSupport a (q.result (fun x => boundedFiniteSupport a x.val) () T).val -
              minimumValue 1 (boundedFiniteSupport a)}

theorem supportHardnessInput_of_gaussian_adaptive {cprob : ℝ}
    (hadapt : GaussianAdaptiveHardnessInput E cprob) :
    SupportHardnessInput E (1 / 512) cprob (1 / 4) 256 := by
  intro k hk hd hkd
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have hkd' : (k : ℝ) ≤ (Module.finrank ℝ E : ℝ) / 512 := by linarith
  exact ⟨gaussianSupportPrior E k, inferInstance, gaussianSupportPrior_negative_event hd hk hkd',
    hadapt k hk hd hkd'⟩

theorem gaussian_adaptive_hardness_small_dimension (hd : Module.finrank ℝ E ≤ 1023) :
    GaussianAdaptiveHardnessInput E (1 / 128) := by
  intro k hk hdmin hkd T hT S mS q hq
  have hk1 : k = 1 := by
    have hd' : (Module.finrank ℝ E : ℝ) ≤ 1023 := by exact_mod_cast hd
    have hklt : (k : ℝ) < 2 := by linarith
    have hklt' : k < 2 := by exact_mod_cast hklt
    omega
  subst k
  have hT' : (T : ℝ) ≤ (Module.finrank ℝ E : ℝ) / 128 := by
    simpa only [Nat.cast_one, mul_one, Real.log_exp, div_one, one_div_mul_eq_div] using hT
  apply (gaussianSupportPrior_single_output_gap q hq T (by omega) hT').trans
  apply measureReal_mono _ (measure_ne_top _ _)
  intro a ha
  simp only [Set.mem_setOf_eq, Nat.cast_one, Real.sqrt_one, div_one] at ha ⊢
  linarith

theorem supportHardnessInput_small_dimension (hd : Module.finrank ℝ E ≤ 1023) :
    SupportHardnessInput E (1 / 512) (1 / 128) (1 / 4) 256 :=
  supportHardnessInput_of_gaussian_adaptive (gaussian_adaptive_hardness_small_dimension hd)

end
end Nonsmooth
