import Bilevel.PolishedHistoryChannel
import Bilevel.PolishedCompiledHistoryLaw
import Bilevel.CachedOracleHistoryAlgorithm
import Bilevel.PrimitiveQueryUpperTheorem

/-! One public cached solver, taking the manuscript's public initial points.
Its code depends only on public numerical budgets and these public points. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Bilevel.PolishedHistory
open PrimitiveGeometry PrimitiveQuery BorelAdaptive OracleCode Stateful
open CachedBudgetCalibration CachedParameterChoice
set_option autoImplicit false
set_option maxHeartbeats 1200000

variable {μ L ρ Δ R₀ σf σg : ℝ}

def publicMachineAt (G : Geometry) (μ L ρ Δ ε R₀ σf σg : ℝ) (x₀ : G.X) (yinit : G.Y) :
    Machine (of (G.X×G.Y)) (of (FullResponse G.X G.Y))
      (of (Fin (outerCount (CachedUpper.universalCurvature L μ L L L ρ) Δ ε))) (of G.X) := by
  let Λ := CachedUpper.universalCurvature L μ L L L ρ
  letI : NeZero (outerCount Λ Δ ε) := ⟨(outerCount_pos Λ Δ ε).ne'⟩
  exact compile (0,0) (0,0)
    (CachedOracleCode.selectedAlgorithm (X:=G.X) (Y:=G.Y)
      μ L L L ρ σf σg Λ Δ ε R₀ x₀ yinit)

def publicAlgorithmAt (G : Geometry) (μ L ρ Δ ε R₀ σf σg : ℝ)
    (x₀ : G.X) (yinit : G.Y) : Algorithm G := by
  let Λ := CachedUpper.universalCurvature L μ L L L ρ
  letI : NeZero (outerCount Λ Δ ε) := ⟨(outerCount_pos Λ Δ ε).ne'⟩
  let m := publicMachineAt G μ L ρ Δ ε R₀ σf σg x₀ yinit
  exact {
    Private := Fin (outerCount Λ Δ ε)
    State := m.state
    privateLaw := StochasticOuter.uniformLaw (outerCount Λ Δ ε)
    program := channelProgram m.program (fun q => pack q.1 q.2)
      (PrimitiveQuery.decode (X:=G.X) (Y:=G.Y)) packLinear.continuous.measurable decode_measurable
    start := m.start
    start_measurable := m.start_measurable }

variable {G : Geometry} (I : Instance G μ L ρ Δ R₀ σf σg)

theorem Instance.upper_canonical_response_eq (x : G.X) :
    I.primitive.canonicalResponse.y x=I.response.y x :=
  I.primitive.lower_solution_unique x _ _ (I.primitive.canonicalResponse.minimizes x) (I.response.minimizes x)

theorem Instance.upper_canonical_hyperobjective :
    I.primitive.hyperobjective I.primitive.canonicalResponse=I.primitive.hyperobjective I.response := by
  funext x
  unfold Model.Primitive.hyperobjective
  rw [I.upper_canonical_response_eq]

theorem Instance.upper_canonical_lower_bound (x : G.X) :
    I.gap.floor≤I.primitive.hyperobjective I.primitive.canonicalResponse x := by
  rw [I.upper_canonical_hyperobjective]
  exact I.gap.lower_bound x

theorem Instance.upper_canonical_gap :
    I.primitive.hyperobjective I.primitive.canonicalResponse I.x₀-I.gap.floor≤Δ := by
  rw [I.upper_canonical_hyperobjective]
  exact I.gap.gap

theorem Instance.upper_canonical_initialization :
    ‖I.yinit-I.primitive.canonicalResponse.y I.x₀‖≤R₀ := by
  rw [I.upper_canonical_response_eq]
  exact I.initialization

theorem Instance.upper_loss_eq_canonical (x : G.X) :
    I.loss x=‖gradient (I.primitive.hyperobjective I.primitive.canonicalResponse) x‖ := by
  rw [I.upper_canonical_hyperobjective]
  rfl

theorem Instance.denote_selectedAlgorithm_law (ε : ℝ)
    (j : Fin (outerCount (CachedUpper.universalCurvature L μ L L L ρ) Δ ε)) (h : I.History) :
    let Λ := CachedUpper.universalCurvature L μ L L L ρ
    (OracleCode.History.denote (H:=of I.History) I.oracle.law I.oracle.update I.oracle.update_measurable
      (CachedOracleCode.selectedAlgorithm (X:=G.X) (Y:=G.Y)
        μ L L L ρ σf σg Λ Δ ε R₀ I.x₀ I.yinit)).law (j,h)=
    ((CachedUpper.algorithm I.oracle μ L L L ρ Λ Δ ε R₀ I.x₀ I.yinit).law ((),h)).map
      (fun z => (CachedOracleCode.selected Λ Δ ε I.x₀ (j,z.1),z.2)) := by
  dsimp only
  rw [CachedOracleCode.selectedAlgorithm,OracleCode.History.denote_map,Procedure.map_law]
  change ((OracleCode.History.denote (H:=of I.History) I.oracle.law I.oracle.update I.oracle.update_measurable
    (CachedOracleCode.algorithm μ L L L ρ σf σg _ Δ ε R₀ I.x₀ I.yinit)).law ((),h)).map _=_
  rw [CachedOracleCode.History.denote_algorithm (H:=of I.History) I.oracle]

end Bilevel.PolishedHistory
