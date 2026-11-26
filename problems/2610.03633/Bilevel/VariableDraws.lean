import Bilevel.IndependentStream
import Bilevel.FreshPullback
import Bilevel.InnerSchedule
import Mathlib.MeasureTheory.Function.Floor

/-! Measurable finite procedures whose call count is selected from the query.
An infinite independent seed supply is only the ambient probability space;
the returned value reads exactly the selected finite prefix. -/

noncomputable section
open MeasureTheory

namespace Bilevel.VariableDraws

variable {Query Seed E : Type*} [MeasurableSpace Query] [MeasurableSpace Seed]
  [MeasurableSpace E]

def execute (program : (n : ℕ) → Query → IndependentDraws.Draws Seed n → E)
    (count : Query → ℕ) (q : Query) (s : IndependentStream.Stream Seed) : E :=
  program (count q) q (IndependentStream.project (count q) s)

theorem execute_measurable (program : (n : ℕ) → Query → IndependentDraws.Draws Seed n → E)
    (count : Query → ℕ)
    (hp : ∀ n, Measurable (fun qs : Query × IndependentDraws.Draws Seed n => program n qs.1 qs.2))
    (hc : Measurable count) :
    Measurable (fun qs : Query × IndependentStream.Stream Seed => execute program count qs.1 qs.2) := by
  have hm : Measurable (fun zs : (Query × IndependentStream.Stream Seed) × ℕ =>
      program zs.2 zs.1.1 (IndependentStream.project zs.2 zs.1.2)) := by
    apply measurable_from_prod_countable
    intro n
    exact (hp n).comp (measurable_fst.prodMk ((IndependentStream.project_measurable n).comp measurable_snd))
  exact hm.comp (measurable_id.prodMk (hc.comp measurable_fst))

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [BorelSpace E] [SecondCountableTopology E]
  {ν : Measure Seed} [IsProbabilityMeasure ν]

omit [MeasurableSpace Query] [MeasurableSpace E] [InnerProductSpace ℝ E]
  [BorelSpace E] [SecondCountableTopology E] in
theorem execute_memLp (program : (n : ℕ) → Query → IndependentDraws.Draws Seed n → E)
    (count : Query → ℕ) (q : Query) (center : E)
    (hp : MemLp (fun s => program (count q) q s - center) 2 (IndependentDraws.law ν (count q))) :
    MemLp (fun s => execute program count q s - center) 2 (IndependentStream.law ν) :=
  hp.comp_measurePreserving (IndependentStream.project_preserves ν (count q))

omit [MeasurableSpace Query] [MeasurableSpace E] [InnerProductSpace ℝ E]
  [BorelSpace E] [SecondCountableTopology E] in
theorem execute_mse (program : (n : ℕ) → Query → IndependentDraws.Draws Seed n → E)
    (count : Query → ℕ) (q : Query) (center : E)
    (hp : StronglyMeasurable (program (count q) q)) :
    (∫ s, ‖execute program count q s - center‖ ^ 2 ∂IndependentStream.law ν) =
      ∫ s, ‖program (count q) q s - center‖ ^ 2 ∂IndependentDraws.law ν (count q) :=
  FreshPullback.integral_pullback (IndependentStream.project_preserves ν (count q))
    (fun s => ‖program (count q) q s - center‖ ^ 2) ((hp.sub stronglyMeasurable_const).norm.pow 2)

end Bilevel.VariableDraws

namespace Bilevel.InnerSchedule

theorem iterations_measurable (μ L σ radius : ℝ) :
    Measurable (iterations μ L σ radius) := by
  unfold iterations logarithm
  exact ((measurable_const.max ((measurable_id.const_mul 2).div_const (radius ^ 2))).log.const_mul
    (μ * stepsize μ L σ radius)⁻¹).nat_ceil

end Bilevel.InnerSchedule
