import Nonsmooth.ContinuousProtocol
import Nonsmooth.MeasurableSimulation
import Nonsmooth.Minimax

open MeasureTheory Function
open scoped ENNReal InnerProductSpace Topology
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [mE : MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
    {Ω S : Type} [mΩ : MeasurableSpace Ω] [mS : MeasurableSpace S]

def policyLinearQuery {R : ℝ} (p : Policy Ω S (Feasible E R)) (μ g : ℝ) (ω : Ω) (n : ℕ) (u : E) : E :=
  (p.query n ω (p.run (fun x => extremal μ g u x.val) ω n)).val

theorem continuous_policy_state_measurable {μ g R : ℝ}
    (p : Policy Ω S (Feasible E R)) (hp : p.IsMeasurable) (ω : Ω) :
    ∀ n, @Measurable E S (adaptiveLinearInformation (policyLinearQuery p μ g ω) n) mS
      (fun u => p.run (fun x => extremal μ g u x.val) ω n) := by
  intro n
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hs : @Measurable E S (adaptiveLinearInformation (policyLinearQuery p μ g ω) (n + 1)) mS
        (fun u => p.run (fun x => extremal μ g u x.val) ω n) := ih.mono le_sup_left le_rfl
    have hq := (hp.query n).comp ((measurable_const (a := ω)).prodMk hs)
    have hx := measurable_subtype_coe.comp hq
    have hr : @Measurable E ℝ (adaptiveLinearInformation (policyLinearQuery p μ g ω) (n + 1)) inferInstance
        (fun u => ⟪policyLinearQuery p μ g ω n u, u⟫_ℝ) := measurable_iff_comap_le.mpr le_sup_right
    have hnorm : @Measurable E ℝ (adaptiveLinearInformation (policyLinearQuery p μ g ω) (n + 1)) inferInstance
        (fun u => ‖policyLinearQuery p μ g ω n u‖) := continuous_norm.measurable.comp hx
    have hval : @Measurable E ℝ (adaptiveLinearInformation (policyLinearQuery p μ g ω) (n + 1)) inferInstance
        (fun u => μ / 2 * ‖policyLinearQuery p μ g ω n u‖ ^ 2 - g * ⟪policyLinearQuery p μ g ω n u, u⟫_ℝ) :=
      ((hnorm.pow_const 2).const_mul (μ / 2)).sub (hr.const_mul g)
    have he : (fun u => μ / 2 * ‖policyLinearQuery p μ g ω n u‖ ^ 2 - g * ⟪policyLinearQuery p μ g ω n u, u⟫_ℝ) =
        (fun u => extremal μ g u (p.query n ω (p.run (fun x => extremal μ g u x.val) ω n)).val) := by
      funext u
      simp only [extremal, policyLinearQuery]
      rw [real_inner_comm]
    rw [he] at hval
    exact (hp.update n).comp (measurable_const.prodMk (hs.prodMk hval))

theorem continuous_policy_query_measurable {μ g R : ℝ}
    (p : Policy Ω S (Feasible E R)) (hp : p.IsMeasurable) (ω : Ω) (n : ℕ) :
    @Measurable E E (adaptiveLinearInformation (policyLinearQuery p μ g ω) n) mE
      (policyLinearQuery p μ g ω n) :=
  measurable_subtype_coe.comp ((hp.query n).comp ((measurable_const (a := ω)).prodMk
    (continuous_policy_state_measurable p hp ω n)))


end
end Nonsmooth
