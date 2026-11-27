import Nonsmooth.AdaptiveOutput
import Nonsmooth.ContinuousPolicy
import Nonsmooth.PriorRisk

open MeasureTheory Function Filter
open scoped ENNReal InnerProductSpace Topology
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [mE : MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  {Ω S : Type} [MeasurableSpace Ω] [mS : MeasurableSpace S]

def linearPolicyOutput (p : Policy Ω S (Feasible E 1)) (c : ℝ) (ω : Ω) (T : ℕ) (u : E) : E :=
  (p.result (fun x => c * ⟪u, x.val⟫_ℝ) ω T).val

theorem linearPolicyOutput_known (p : Policy Ω S (Feasible E 1)) (hp : p.IsMeasurable)
    (c : ℝ) (ω : Ω) (T : ℕ) :
    @Measurable E E (adaptiveLinearInformation (policyLinearQuery p 0 (-c) ω) T) mE
      (linearPolicyOutput p c ω T) := by
  have hm := measurable_subtype_coe.comp ((hp.output).comp ((measurable_const (a := ω)).prodMk
    (continuous_policy_state_measurable (μ := 0) (g := -c) p hp ω T)))
  convert! hm using 1
  funext u
  simp only [linearPolicyOutput, Policy.result, extremal, zero_div, zero_mul, Function.comp_def,
      neg_mul, zero_sub, neg_neg]

theorem linear_policy_output_negative_tail (p : Policy Ω S (Feasible E 1)) (hp : p.IsMeasurable)
    (c : ℝ) (ω : Ω) (T : ℕ) (hT : T + 1 ≤ Module.finrank ℝ E) :
    (sphericalLaw E).real {u : E | ⟪linearPolicyOutput p c ω T u, u⟫_ℝ < -1 / 2} ≤
      4 * ((T : ℝ) + 1) / (Module.finrank ℝ E : ℝ) := by
  apply spherical_adaptive_output_negative_tail (policyLinearQuery p 0 (-c) ω)
    (linearPolicyOutput p c ω T) T hT
    (fun n _ => continuous_policy_query_measurable p hp ω n)
    (linearPolicyOutput_known p hp c ω T)
  exact Eventually.of_forall (fun u => (p.result (fun x => c * ⟪u, x.val⟫_ℝ) ω T).property)

theorem linear_policy_output_tail_eighth (p : Policy Ω S (Feasible E 1)) (hp : p.IsMeasurable)
    (c : ℝ) (ω : Ω) (T : ℕ) (hd : 86 ≤ Module.finrank ℝ E)
    (hT : (T : ℝ) ≤ (Module.finrank ℝ E : ℝ) / 128) :
    (sphericalLaw E).real {u : E | ⟪linearPolicyOutput p c ω T u, u⟫_ℝ < -1 / 2} ≤ 1 / 8 := by
  have hd' : (86 : ℝ) ≤ Module.finrank ℝ E := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < Module.finrank ℝ E := by positivity
  have hbudget : T + 1 ≤ Module.finrank ℝ E := by
    have h : (T : ℝ) + 1 ≤ (Module.finrank ℝ E : ℝ) := by linarith
    exact_mod_cast h
  exact (linear_policy_output_negative_tail p hp c ω T hbudget).trans
    ((div_le_iff₀ hdpos).mpr (by linarith))

theorem linearPolicyOutput_joint_measurable (p : Policy Ω S (Feasible E 1)) (hp : p.IsMeasurable)
    (ω : Ω) (T : ℕ) : Measurable (fun z : ℝ × E => linearPolicyOutput p z.1 ω T z.2) := by
  have hf : Measurable (Function.uncurry (fun (z : ℝ × E) (x : Feasible E 1) => z.1 * ⟪z.2, x.val⟫_ℝ)) :=
    (measurable_fst.comp measurable_fst).mul
      ((continuous_fst.inner continuous_snd).measurable.comp
        ((measurable_snd.comp measurable_fst).prodMk (measurable_subtype_coe.comp measurable_snd)))
  exact measurable_subtype_coe.comp ((family_policy_output_measurable hp
    (fun (z : ℝ × E) (x : Feasible E 1) => z.1 * ⟪z.2, x.val⟫_ℝ) hf T).comp
      (measurable_id.prodMk measurable_const))

end
end Nonsmooth
