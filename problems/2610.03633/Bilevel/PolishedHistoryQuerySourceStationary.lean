import Bilevel.PolishedHistoryQuerySource
import Bilevel.PolishedHistorySourcePostRun

/-! Genuine stationary fresh executions are legal in the query-adapted
source model. No full-state/full-private-information hypothesis is imposed
on arbitrary source executions; that information is merely a valid choice
for these constructed fresh witnesses. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Bilevel.PolishedHistory
open PrimitiveQuery
set_option autoImplicit false
variable {G : Geometry} {μ L ρ Δ R₀ σf σg : ℝ}
variable (I : PrimitiveQuery.Instance G μ L ρ Δ R₀ σf σg)

/-- The actual private-seed/stream path, with pointwise program recursion
and proved conditional moments, is a source challenge. -/
def stationaryQueryExecution (A : Algorithm G) :
    QuerySourceExecution (stationarySourceMean I) A σf σg where
  Ω:=(stationarySourceExecution I A).Ω
  law:=(stationarySourceExecution I A).law
  privateSeed:=(stationarySourceExecution I A).privateSeed
  private_measurable:=(stationarySourceExecution I A).private_measurable
  private_law:=(stationarySourceExecution I A).private_law
  state:=(stationarySourceExecution I A).state
  obs:=(stationarySourceExecution I A).obs
  sample:=(stationarySourceExecution I A).sample
  sample_measurable:=(stationarySourceExecution I A).sample_measurable
  obs_eq:=(stationarySourceExecution I A).obs_eq
  state_measurable:=(stationarySourceExecution I A).state_measurable
  obs_measurable:=(stationarySourceExecution I A).obs_measurable
  init:=freshSourceState_initial I A
  next:=freshSourceState_next I A
  information:=(stationarySourceExecution I A).information
  information_le:=(stationarySourceExecution I A).information_le
  information_mono:=(stationarySourceExecution I A).information_mono
  obs_information:=(stationarySourceExecution I A).obs_information
  query_information:=fun n => A.program.query_measurable.comp (freshSourceState_information I A n)
  upper_square_integrable:=(stationarySourceExecution I A).upper_square_integrable
  lower_square_integrable:=(stationarySourceExecution I A).lower_square_integrable
  upper_mean:=(stationarySourceExecution I A).upper_mean
  lower_mean:=(stationarySourceExecution I A).lower_mean
  upper_variance:=(stationarySourceExecution I A).upper_variance
  lower_variance:=(stationarySourceExecution I A).lower_variance

theorem stationaryQueryExecution_cost (A : Algorithm G) : (stationaryQueryExecution I A).cost=I.cost A := rfl

theorem stationaryQueryExecution_risk (A : Algorithm G) : (stationaryQueryExecution I A).risk=I.risk A := rfl

theorem stationaryQueryExecution_conservative (A : Algorithm G) (hI : I.IsConservative) :
    (stationaryQueryExecution I A).IsConservative := stationarySourceExecution_conservative I A hI

theorem query_post_compile_cost (P : PostAlgorithm G) :
    I.cost P.compile=(stationaryQueryExecution I P.bodyAsAlgorithm).cost := post_compile_cost I P

theorem query_post_compile_risk (P : PostAlgorithm G) :
    I.risk P.compile=(stationaryQueryExecution I P.bodyAsAlgorithm).postRisk := post_compile_risk I P

def stationaryQueryPostChallenge (A : PostSolverAt) : QueryPostChallenge A μ L ρ Δ R₀ σf σg where
  geometry:=G
  mean:=stationarySourceMean I
  execution:=stationaryQueryExecution I (A G 0 0).bodyAsAlgorithm

end Bilevel.PolishedHistory
