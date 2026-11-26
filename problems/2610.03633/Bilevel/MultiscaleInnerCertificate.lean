import Bilevel.MultiscaleBoundedGapWitness
import Bilevel.MultiscalePrimitiveOracles

/-! A retained actual Primitive and its exact scalar identities, response,
gap, curvature and blind-coordinate margin. -/
noncomputable section
namespace Bilevel.MultiscaleMean
open CompensatedMean Filter
set_option autoImplicit false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {n : ℕ}

def InnerPrimitiveCertificate (P : Parameters (E:=E) n) (μ L ρ Δ C κ ε : ℝ) : Prop :=
  ∃ Q : Model.Primitive (X:=E) (Y:=LowerSpace E) μ L L L ρ, ∃ r : Q.Response,
    Q.f=P.data.upper ∧ Q.g=P.data.lower ∧ r.y=P.data.response ∧
    Q.hyperobjective r=P.realized ∧ r.y 0=0 ∧ Nonempty (Q.GapCertificate r 0 Δ) ∧
    Tendsto (Q.hyperobjective r) (cocompact E) atTop ∧
    (∀ x z,‖gradient (Q.hyperobjective r) x-gradient (Q.hyperobjective r) z‖≤(C*L*κ^2)*‖x-z‖) ∧
    (∀ x,|WrappedChain.coordinates n P.R P.U ((P.L/P.μ) • x) (Fin.last n)|<P.β →
      8*ε≤‖gradient (Q.hyperobjective r) x‖)

theorem InnerPrimitiveCertificate.barrier {P : Parameters (E:=E) n} {μ L ρ Δ C κ ε : ℝ}
    (H : InnerPrimitiveCertificate P μ L ρ Δ C κ ε) (x : E)
    (hx : |WrappedChain.coordinates n P.R P.U ((P.L/P.μ) • x) (Fin.last n)|<P.β) :
    8*ε≤ innerOriginalLoss P x := by
  obtain ⟨Q,r,_hf,_hg,_hr,hmean,_hz,_hgap,_hcoerc,_hcurv,hblind⟩ := H
  have hh := hblind x hx
  simpa only [hmean,innerOriginalLoss] using hh

end Bilevel.MultiscaleMean
