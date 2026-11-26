import Bilevel.PrimitiveQueryModel
import Bilevel.PrimitiveQueryHistorySFO
import Bilevel.PrimitiveQueryCanonicalResponse
import Bilevel.CachedOracleCodeAlgorithm
import Bilevel.OracleSelectedLaw
import Bilevel.CachedUpperRateTheorem
import Bilevel.ChiUpperTheorem
import Bilevel.BorelAdaptiveChannelTransport
import Mathlib.Probability.UniformOn

/-! The public cached upper code as a `PrimitiveQuery.Solver`.

The code is compiled once from the public numerical budgets.  A channel
adapter changes the raw `(X × Y)` query used by the cached code into the
public L2 joint query carried by `Geometry`; it decodes the two joint replies
back to the full paired response.  No primitive, response, truth, or hidden
seed law occurs in this construction.
-/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Bilevel.PrimitiveQuery
open PrimitiveGeometry BorelAdaptive OracleCode Stateful
open CachedBudgetCalibration CachedParameterChoice
set_option autoImplicit false

variable {X Y : Type}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)]
  [SecondCountableTopology (Joint X Y)] [FiniteDimensional ℝ X]
  [FiniteDimensional ℝ Y] [Nontrivial Y]

variable {μ L ρ Δ R₀ σf σg : ℝ}

def unpack (q : Joint X Y) : X × Y := (q.1,q.2)

omit [CompleteSpace X] [SecondCountableTopology X] [CompleteSpace Y]
  [SecondCountableTopology (Joint X Y)] [FiniteDimensional ℝ X]
  [FiniteDimensional ℝ Y] [Nontrivial Y] in
theorem unpack_measurable : Measurable (unpack (X:=X) (Y:=Y)) := by
  exact (WithLp.prodContinuousLinearEquiv 2 ℝ X Y).continuous.measurable

def decode (r : (Joint X Y) × (Joint X Y)) : (X × Y) × (X × Y) :=
  (unpack r.1,unpack r.2)

omit [CompleteSpace X] [SecondCountableTopology X] [CompleteSpace Y]
  [SecondCountableTopology (Joint X Y)] [FiniteDimensional ℝ X]
  [FiniteDimensional ℝ Y] [Nontrivial Y] in
theorem decode_measurable : Measurable (decode (X:=X) (Y:=Y)) := by
  exact ((unpack_measurable (X:=X) (Y:=Y)).comp measurable_fst).prodMk
    ((unpack_measurable (X:=X) (Y:=Y)).comp measurable_snd)

def rawReply (I : Instance (Geometry.of X Y) μ L ρ Δ R₀ σf σg)
    (_ : Unit) (q : X × Y) (c : I.Seed) : (X × Y) × (X × Y) :=
  (I.upper.sample (pack q.1 q.2) c,I.lower.sample (pack q.1 q.2) c)

def encodedReply (I : Instance (Geometry.of X Y) μ L ρ Δ R₀ σf σg)
    (_ : Unit) (q : Joint X Y) (c : I.Seed) : (Joint X Y) × (Joint X Y) :=
  I.reply () q c

theorem decode_encodedReply (I : Instance (Geometry.of X Y) μ L ρ Δ R₀ σf σg)
    (q : X × Y) (c : I.Seed) :
    decode (encodedReply I () (pack q.1 q.2) c)=rawReply I () q c := by
  rfl

def publicMachine (G : Geometry) (μ L ρ Δ ε R₀ : ℝ) (σf σg : ℝ) :
    OracleCode.Machine (of (G.X × G.Y)) (of (Stateful.FullResponse G.X G.Y))
      (of (Fin (outerCount (CachedUpper.universalCurvature L μ L L L ρ) Δ ε))) (of G.X) := by
  let Λ := CachedUpper.universalCurvature L μ L L L ρ
  letI : NeZero (outerCount Λ Δ ε) := ⟨(outerCount_pos Λ Δ ε).ne'⟩
  exact OracleCode.compile (0,0) (0,0)
    (CachedOracleCode.selectedAlgorithm (X:=G.X) (Y:=G.Y)
      μ L L L ρ σf σg Λ Δ ε R₀ (0:G.X) (0:G.Y))

def publicAlgorithm (G : Geometry) (μ L ρ Δ ε R₀ σf σg : ℝ) : Algorithm G := by
  let Λ := CachedUpper.universalCurvature L μ L L L ρ
  letI : NeZero (outerCount Λ Δ ε) := ⟨(outerCount_pos Λ Δ ε).ne'⟩
  let m := publicMachine G μ L ρ Δ ε R₀ σf σg
  exact {
    Private := Fin (outerCount Λ Δ ε)
    State := m.state
    privateLaw := StochasticOuter.uniformLaw (outerCount Λ Δ ε)
    program := BorelAdaptive.channelProgram m.program
      (fun q => pack q.1 q.2) (decode (X:=G.X) (Y:=G.Y))
      ((packLinear (X:=G.X) (Y:=G.Y)).continuous.measurable)
      (decode_measurable (X:=G.X) (Y:=G.Y))
    start := m.start
    start_measurable := m.start_measurable }

end Bilevel.PrimitiveQuery
