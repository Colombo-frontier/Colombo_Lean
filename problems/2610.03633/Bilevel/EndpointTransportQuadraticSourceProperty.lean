import Bilevel.EndpointTransportQuadraticObjective

/-! Shared analytic certificate for one concrete physical quadratic family. -/
noncomputable section
open Filter
open scoped Topology
namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry ChiRecursive ChiCarrier
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def QuadraticSourceProperty {n D : ℕ} (Q : Rotations n D) (M : Node E)
    (G : Geometry (Block D)) (ρ R : ℕ → ℝ) (L Δ ε ℓ b K Kg : ℝ) : Prop :=
  let f := quadraticCore Q M (ℓ/24) G (ρ 0) (R 0)
  let Ftrue := quadraticSourceMean M (ℓ/24) G ρ R K
  (G 0 []).ell=ℓ ∧ (G 0 []).width=b/Kg ∧
  (∀ z : Joint E (Physical n D),‖iteratedFDeriv ℝ 2 f z‖≤L/4 ∧
    ‖gradient (fun u => f (pack z.fst u)) z.snd‖≤L/4) ∧
  Tendsto Ftrue (cocompact (Joint E (Blocks 1 (Block D)))) atTop ∧ Ftrue 0=0 ∧
  Ftrue 0-sInf (Set.range Ftrue)≤Δ ∧
  ∀ z : Joint E (Blocks 1 (Block D)),M.coordinates z.fst (Fin.last M.n)<b → 8*ε≤‖gradient Ftrue z‖

end Bilevel.EndpointTransportResponse
