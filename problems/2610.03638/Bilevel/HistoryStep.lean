import Bilevel.HistoryOracle
import Bilevel.StatefulProcedureLaws
import Bilevel.StochasticInner

/-! An executed affine update from one original history-dependent call. -/
noncomputable section
open MeasureTheory ProbabilityTheory

namespace Bilevel.Stateful.HistoryOracle
variable {Query History Obs E Param : Type*} [MeasurableSpace Query]
  [MeasurableSpace History] [MeasurableSpace Obs] [MeasurableSpace Param]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {σ : ℝ} (O : HistoryOracle (Query := Query) (History := History) (Obs := Obs) (E := E) σ)

def step (q : Param → Query) (hq : Measurable q) (d : Param → E)
    (hd : Measurable d) (η : Param → ℝ) (hη : Measurable η) : Procedure Param History E :=
  (O.call.reparam q hq).map (fun z => d z.1 - η z.1 • z.2)
    ((hd.comp measurable_fst).sub ((hη.comp measurable_fst).smul measurable_snd))

omit [CompleteSpace E] in
theorem step_calls (q : Param → Query) (hq : Measurable q) (d : Param → E)
    (hd : Measurable d) (η : Param → ℝ) (hη : Measurable η) :
    (O.step q hq d hd η hη).CallsEq (fun _ => 1) :=
  Procedure.CallsEq.map _ _ (Procedure.CallsEq.reparam _ _ O.call_calls q hq) _ _

theorem affine_error (q : Query) (h : History) (d center : E) (η : ℝ) :
    Integrable (fun o => ‖d - η • O.read o - center‖ ^ 2) (O.law (q,h)) ∧
      (∫ o, ‖d - η • O.read o - center‖ ^ 2 ∂O.law (q,h)) =
        ‖d - η • O.truth q - center‖ ^ 2 +
          η ^ 2 * (∫ o, ‖O.read o - O.truth q‖ ^ 2 ∂O.law (q,h)) := by
  have he : (fun o => d - η • O.read o - center) =
      fun o => (d - η • O.truth q - center) - η • (O.read o - O.truth q) := by
    funext o
    simp only [smul_sub]
    abel
  have hlp : MemLp (fun o => d - η • O.read o - center) 2 (O.law (q,h)) := by
    rw [he]
    exact (memLp_const _).sub ((O.error_memLp q h).const_smul η)
  refine ⟨(memLp_two_iff_integrable_sq_norm hlp.aestronglyMeasurable).mp hlp, ?_⟩
  simp_rw [congrFun he]
  exact StochasticInner.fixed_step_identity _ _ η (O.error_integrable q h)
    (O.square_integrable q h) (O.mean q h)

theorem step_error (q : Param → Query) (hq : Measurable q) (d : Param → E)
    (hd : Measurable d) (η : Param → ℝ) (hη : Measurable η)
    (p : Param) (h : History) (center : E) :
    Integrable (fun z => ‖z.1 - center‖ ^ 2) ((O.step q hq d hd η hη).law (p,h)) ∧
      (∫ z, ‖z.1 - center‖ ^ 2 ∂(O.step q hq d hd η hη).law (p,h)) ≤
        ‖d p - η p • O.truth (q p) - center‖ ^ 2 + (η p) ^ 2 * σ ^ 2 := by
  have hg : StronglyMeasurable (fun v : E => ‖v-center‖ ^ 2) :=
    (by fun_prop : Measurable (fun v : E => ‖v-center‖ ^ 2)).stronglyMeasurable
  have hm : Measurable (fun o => (O.read o, O.update ((q p,h),o), 1)) :=
    O.finish_measurable.comp (measurable_const.prodMk measurable_id)
  have hf : StronglyMeasurable (fun z : Outcome E History => ‖d p - η p • z.1-center‖ ^ 2) :=
    (by fun_prop : Measurable (fun z : Outcome E History => ‖d p - η p • z.1-center‖ ^ 2)).stronglyMeasurable
  have ha := O.affine_error (q p) h (d p) center (η p)
  constructor
  · rw [step, Procedure.map_output_integrable_iff _ _ _ _ _ _ hg]
    change Integrable (fun z => ‖d p - η p • z.1-center‖ ^ 2) (O.call.law (q p,h))
    rw [O.call_law]
    exact (integrable_map_measure hf.aestronglyMeasurable hm.aemeasurable).mpr ha.1
  · rw [step, Procedure.map_output_integral _ _ _ _ _ _ hg]
    change (∫ z, ‖d p - η p • z.1-center‖ ^ 2 ∂O.call.law (q p,h)) ≤ _
    rw [O.call_law, integral_map hm.aemeasurable hf.aestronglyMeasurable, ha.2]
    exact add_le_add_left (mul_le_mul_of_nonneg_left (O.variance (q p) h) (sq_nonneg _)) _

end Bilevel.Stateful.HistoryOracle
