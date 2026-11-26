import Bilevel.PrimitiveGeometry
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Finite-dimensional public geometry for the original-query minimax model.
An algorithm may depend on this geometry and the public numerical budgets,
but the geometry does not contain the hidden objectives or an oracle law. -/
noncomputable section
namespace Bilevel.PrimitiveQuery
open PrimitiveGeometry

structure Geometry where
  X : Type
  Y : Type
  [normedX : NormedAddCommGroup X]
  [innerX : InnerProductSpace ℝ X]
  [completeX : CompleteSpace X]
  [finiteX : FiniteDimensional ℝ X]
  [measurableX : MeasurableSpace X]
  [borelX : BorelSpace X]
  [countableX : SecondCountableTopology X]
  [normedY : NormedAddCommGroup Y]
  [innerY : InnerProductSpace ℝ Y]
  [completeY : CompleteSpace Y]
  [finiteY : FiniteDimensional ℝ Y]
  [nontrivialY : Nontrivial Y]
  [measurableY : MeasurableSpace Y]
  [borelY : BorelSpace Y]
  [countableY : SecondCountableTopology Y]
  [measurableQuery : MeasurableSpace (Joint X Y)]
  [borelQuery : BorelSpace (Joint X Y)]
  [countableQuery : SecondCountableTopology (Joint X Y)]

attribute [instance] Geometry.normedX Geometry.innerX Geometry.completeX
  Geometry.finiteX Geometry.measurableX Geometry.borelX Geometry.countableX
  Geometry.normedY Geometry.innerY Geometry.completeY Geometry.finiteY
  Geometry.nontrivialY
  Geometry.measurableY Geometry.borelY Geometry.countableY
  Geometry.measurableQuery Geometry.borelQuery Geometry.countableQuery

abbrev Geometry.Query (G : Geometry) := Joint G.X G.Y
abbrev Geometry.Reply (G : Geometry) := G.Query × G.Query

def Geometry.of (X Y : Type)
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    [FiniteDimensional ℝ Y] [Nontrivial Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)]
    [SecondCountableTopology (Joint X Y)] : Geometry where
  X := X
  Y := Y

end Bilevel.PrimitiveQuery
