import Bilevel.PolishedHistorySourcePost

/-! Every ordinary randomized Borel algorithm is represented by an
arbitrary-body, independent-terminal source algorithm: take a unit terminal
seed and the identity terminal readout. No program syntax is restricted. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Bilevel.PolishedHistory.PostAlgorithm
open PrimitiveQuery PrimitiveGeometry Stateful BorelAdaptive
set_option autoImplicit false
variable {G : Geometry}

def ofAlgorithm (A : Algorithm G) : PostAlgorithm G where
  Private:=A.Private
  State:=A.State
  Output:=G.X
  Terminal:=Unit
  privateLaw:=A.privateLaw
  body:={
    query:=fun s => PrimitiveQuery.unpack (A.program.query s)
    query_measurable:=PrimitiveQuery.unpack_measurable.comp A.program.query_measurable
    update:=fun z => A.program.update (z.1,packResponse z.2)
    update_measurable:=A.program.update_measurable.comp
      (measurable_fst.prodMk (packResponse_measurable.comp measurable_snd))
    halt:=A.program.halt
    halt_measurable:=A.program.halt_measurable
    output:=A.program.output
    output_measurable:=A.program.output_measurable }
  start:=A.start
  start_measurable:=A.start_measurable
  terminalLaw:=Measure.dirac ()
  select:=Prod.snd
  select_measurable:=measurable_snd

/-- The query/update/halt/output program is preserved exactly after the
public raw-coordinate channel conversion. -/
theorem ofAlgorithm_packedBody (A : Algorithm G) : (ofAlgorithm A).packedBody=A.program := by
  rfl

end Bilevel.PolishedHistory.PostAlgorithm
