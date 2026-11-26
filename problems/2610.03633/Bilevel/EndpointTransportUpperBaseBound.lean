import Bilevel.EndpointTransportUpperBase
noncomputable section
set_option maxHeartbeats 300000
namespace Bilevel.EndpointTransportResponse
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry PartialLegendre
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
theorem physicalUpperBase_second_bound {n D : ℕ} (m : ℕ) (Q : Rotations n D) (M : Node E) (ν : ℝ)
    (G : Geometry (Block D)) (d : ℕ) (ρ R : ℝ) (z : PhysicalBase E m n D) (Bm Bl : ℝ)
    (hm : ‖iteratedFDeriv ℝ 2 (macroValue M.n M.ell M.width ν M.radius M.frame) z.fst‖≤Bm)
    (hl : ‖iteratedFDeriv ℝ 2 (physicalBaseLower m Q M G d ρ R) z‖≤Bl) :
    ‖iteratedFDeriv ℝ 2 (physicalUpperBase m Q M ν G d ρ R) z‖≤Bm+Bl := by
  let P : PhysicalBase E m n D →L[ℝ] E := baseMacroProjection (E:=E) m n D
  let f : E → ℝ := macroValue M.n M.ell M.width ν M.radius M.frame
  have he : physicalUpperBase m Q M ν G d ρ R=
      fun x => (f ∘ P) x+physicalBaseLower m Q M G d ρ R x := rfl
  rw [he]
  have hc := (macro_contDiff M ν 3).comp P.contDiff
  have hj := linear_jet_contraction P (baseMacroProjection_norm_le (E:=E) m n D)
    (macro_contDiff M ν 3) z 2 (by norm_num)
  have hpoint : P z=z.fst := rfl
  rw [hpoint] at hj
  exact scalar_add_jet_bound (f ∘ P) (physicalBaseLower m Q M G d ρ R)
    hc (physicalBaseLower_contDiff m Q M G d ρ R) z 2
    (by norm_num) Bm Bl (hj.trans hm) hl


end Bilevel.EndpointTransportResponse
