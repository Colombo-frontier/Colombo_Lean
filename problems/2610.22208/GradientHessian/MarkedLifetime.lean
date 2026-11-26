import GradientHessian.ForkMachineBound
import GradientHessian.ForkLifetime

/-!
# The marked-task lifetime for actual machines

This combines the charged chronological machine bound, the actual normalized
Gaussian source-event probability, and the explicit absolute lifetime constants.
`M` may be the manuscript value `1+4096*J^2` or any larger budget parameter.
-/

namespace GradientHessian.MarkedLifetime

open Matrix MeasureTheory LowRank OracleComposition ForkMachineBound ForkChronologicalProbability
noncomputable section

variable {Seed PreState PostState Private : Type*}
  [MeasurableSpace Seed] [MeasurableSpace PreState] [MeasurableSpace PostState]
  [MeasurableSpace Private]

/-- Source `cor:lifetime` for the literal selected-test event. Previous
readout disclosures are charged, private seeds are independent, and no finite
internal-time or eventual probability estimate is assumed. The output register
retains the genuinely selected tests, as specified by `RetainsTests`. -/
theorem source_machine_lifetime (M r J κ q₀ S q₁ a b : ℕ)
    (hMsource : 1+4096*J^2 ≤ M) (hJ : ForkLifetime.depthThreshold ≤ J)
    (hr : ForkLifetime.rankRatio*(M:ℝ) ≤ r) (hκ : 18874368 ≤ κ)
    (hS : S ≤ M) (hq₀ : q₀ ≤ M*ForkLifetime.lifetime J+1)
    (hq₁ : q₁ ≤ ForkLifetime.lifetime J+1)
    (hab : κ*r+b=a) (hD : a+totalBudget J q₀ S r q₁=κ*r*J)
    {P : Matrix (Fin (a+totalBudget J q₀ S r q₁)) (Fin (a+totalBudget J q₀ S r q₁)) ℝ}
    (hP : IsOrthogonalProjector P) (hrank : P.rank = r)
    (B : Matrix (Fin (a+totalBudget J q₀ S r q₁)) (Fin r) ℝ) (hB : Bᵀ*B = 1) (hPB : P*B = B)
    (fallback : Fin (a+totalBudget J q₀ S r q₁) → ℝ)
    (pre : DisclosureCompiler.Program (a+totalBudget J q₀ S r q₁) PreState)
    (post : MachineCompiler.Program (a+totalBudget J q₀ S r q₁) PostState
      (Fin (q₁+2) → EuclideanSpace ℝ (Fin (a+totalBudget J q₀ S r q₁))))
    (preInitial : MeasurableStateMap Seed PreState)
    (postInitial : MeasurableStateMap (PreState × (EuclideanSpace ℝ (Fin r) × Private)) PostState)
    (enabled : MeasurableStateMap PreState Bool)
    (hlegal : Legal (n := b+totalBudget J q₀ S r q₁)
      pre post preInitial postInitial enabled J P fallback q₀ S q₁)
    (hretain : RetainsTests post)
    (seedLaw : Measure Seed) [IsProbabilityMeasure seedLaw]
    (privateLaw : Measure Private) [IsProbabilityMeasure privateLaw] :
    (experimentLaw (r := r) J P
      (iidMatrixLaw (a+totalBudget J q₀ S r q₁) (b+totalBudget J q₀ S r q₁)
        ((a+totalBudget J q₀ S r q₁:ℕ):NNReal)⁻¹) seedLaw privateLaw).real
      (eventualHit pre post preInitial postInitial enabled J P B fallback ForkLifetime.gamma) ≤ 1/256 ∧
    (ForkLifetime.lifetimeFraction/2)*(J:ℝ) ≤ ForkLifetime.lifetime J ∧
      1 ≤ (ForkLifetime.lifetimeFraction/2)*(J:ℝ) := by
  have hM : 1 ≤ M := by omega
  have hparams := ForkLifetime.source_parameters hM hJ hr
  have hr0 : 0 < r := by omega
  have hκ0 : 0 < κ := by omega
  have hkr := Nat.mul_pos hκ0 hr0
  have ha0 : 0 < a := by omega
  have hb : b ≤ a := by omega
  have hsource : 1+4096*J^2 ≤ r := hMsource.trans hparams.2.1
  have hpE := source_event_mass a b (totalBudget J q₀ S r q₁) J κ (κ*r) r
    hparams.1 hsource hκ rfl hab hD P hP hrank
  have hp : 0 < (iidMatrixLaw (a+totalBudget J q₀ S r q₁) (b+totalBudget J q₀ S r q₁)
      ((a+totalBudget J q₀ S r q₁:ℕ):NNReal)⁻¹).real
      (MatrixKernelConcentration.sourceGoodEvent P J) := by linarith
  have hv : ((a+totalBudget J q₀ S r q₁:ℕ):NNReal)⁻¹ ≠ 0 := by
    apply inv_ne_zero
    exact_mod_cast (show a+totalBudget J q₀ S r q₁ ≠ 0 by omega)
  have hδ : 5*ReadoutFilter.delta ≤ ForkLifetime.gamma/4 := by
    norm_num [ReadoutFilter.delta_eq,ForkLifetime.gamma]
  have hf := eventual_fork_bound a b J q₀ S q₁ r hb ha0 hparams.1 hr0 hP B hB hPB fallback
    pre post preInitial postInitial enabled hlegal hretain seedLaw privateLaw hv
    ForkLifetime.gamma_pos hδ hp
  have hn : bound J q₀ S q₁ r a b ForkLifetime.gamma
      ((iidMatrixLaw (a+totalBudget J q₀ S r q₁) (b+totalBudget J q₀ S r q₁)
        ((a+totalBudget J q₀ S r q₁:ℕ):NNReal)⁻¹).real
        (MatrixKernelConcentration.sourceGoodEvent P J)) ≤ 1/256 :=
    ForkLifetime.source_lifetime_bound hM hJ hr (by omega) hS hq₀ hq₁ hpE hab hD
  exact ⟨hf.trans hn,(ForkLifetime.lifetime_bounds hJ).1,(ForkLifetime.lifetime_bounds hJ).2.1⟩

end
end GradientHessian.MarkedLifetime
