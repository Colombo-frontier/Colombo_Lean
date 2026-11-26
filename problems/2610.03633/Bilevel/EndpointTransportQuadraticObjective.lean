import Bilevel.EndpointTransportQuadraticTrace

/-! Named source objective for the exact-quadratic endpoint family. -/
noncomputable section
namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry ChiRecursive ChiCarrier ChiOuter
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def quadraticSourceMean {D : ℕ} (M : Node E) (ν : ℝ) (G : Geometry (Block D))
    (ρ R : ℕ → ℝ) (K : ℝ) : Joint E (Blocks 1 (Block D)) → ℝ :=
  jointOuter 1 M ν G ρ R 0 K

end Bilevel.EndpointTransportResponse
