import Bilevel.EndpointTransportQuadraticTrace
import Bilevel.ChiPrimitiveObjective

/-! Actual depth-zero transport Primitive, retaining its exact quadratic
lower formula and the original recursive mean under an isometry. -/
noncomputable section
set_option maxHeartbeats 1200000
namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry ChiRecursive ChiCarrier ChiOuter
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem quadratic_core_primitive_of_budgets {D : ℕ} {L κ : ℝ} (hL : 0<L) (hκ : 3200≤κ)
    (Q : Rotations (EndpointTransportNormalization.interiors κ) D)
    (M : Node E) (ν : ℝ) (G : Geometry (Block D)) (ρ R : ℕ → ℝ)
    (hjet : ∀ z,‖iteratedFDeriv ℝ 2 (quadraticCore Q M ν G (ρ 0) (R 0)) z‖≤L/4)
    (hupper : ∀ z : Joint E (Physical (EndpointTransportNormalization.interiors κ) D),
      ‖gradient (fun v => quadraticCore Q M ν G (ρ 0) (R 0) (pack z.fst v)) z.snd‖≤L/4) :
    ∃ P : Model.Primitive (X:=Joint E (Block D))
      (Y:=Physical (EndpointTransportNormalization.interiors κ) D) (L/κ) L L L 0,
      (∀ x y,P.f x y=quadraticCore Q M ν G (ρ 0) (R 0) (pack x.fst y)) ∧
      (∀ x y,P.g x y=lower (L/16) (L/4) Q x.snd y) ∧
      (∀ x y,P.gyy x y=physicalHessian (L/16) Q) ∧
      ∃ r : P.Response,r.y 0=0 ∧
        (∀ x,r.y x=physicalResponse (L/16) (L/4) Q x.snd) ∧
        (∀ x,P.hyperobjective r x=jointOuter 1 M ν G ρ R 0
          (EndpointTransportNormalization.gain κ) (oneBlockCoordinates x)) ∧
        (∀ x y,P.IsLowerSolution x y ↔ y=r.y x) := by
  obtain ⟨P,hf,hg,hyy,r,hrzero,hr,hm,hu⟩ := transport_primitive hL hκ Q
    (quadraticFullCore Q M ν G (ρ 0) (R 0)) (quadraticFullCore_contDiff Q M ν G (ρ 0) (R 0))
    (fun x y => by
      rw [quadraticFullCore_lower_gradient]
      exact (hupper (pack x.fst y)).trans (by linarith only [hL]))
    (fun z => (quadraticFullCore_second_bound Q M ν G (ρ 0) (R 0) (L/4) hjet z).trans
      (by linarith only [hL]))
  refine ⟨P,hf,hg,hyy,r,hrzero,hr,?_,?_⟩
  · intro x
    rw [hm]
    exact source_quadraticCore_response hL hκ Q M ν G ρ R x
  · intro x y
    rw [hr]
    exact hu x y

theorem source_quadratic_gradient_norm {D n : ℕ} {μ Lf Lg Cf ρg κ : ℝ}
    (M : Node E) (ν : ℝ) (G : Geometry (Block D)) (ρ R : ℕ → ℝ)
    (P : Model.Primitive (X:=Joint E (Block D)) (Y:=Physical n D) μ Lf Lg Cf ρg)
    (r : P.Response)
    (hmean : ∀ x,P.hyperobjective r x=jointOuter 1 M ν G ρ R 0
      (EndpointTransportNormalization.gain κ) (oneBlockCoordinates x)) (x : Joint E (Block D)) :
    ‖gradient (P.hyperobjective r) x‖=‖gradient
      (jointOuter 1 M ν G ρ R 0 (EndpointTransportNormalization.gain κ)) (oneBlockCoordinates x)‖ := by
  rw [show P.hyperobjective r=(fun z => jointOuter 1 M ν G ρ R 0
    (EndpointTransportNormalization.gain κ) (oneBlockCoordinates z)) from funext hmean]
  exact oneBlock_gradient_norm _ x
    ((jointOuter_contDiff 1 M ν G ρ R 0 (EndpointTransportNormalization.gain κ) 1).differentiable (by norm_num) _)

theorem source_quadratic_gap_transfer {D n : ℕ} {μ Lf Lg Cf ρg : ℝ}
    (P : Model.Primitive (X:=Joint E (Block D)) (Y:=Physical n D) μ Lf Lg Cf ρg)
    (r : P.Response) (f : Joint E (Blocks 1 (Block D)) → ℝ)
    (hmean : ∀ x,P.hyperobjective r x=f (oneBlockCoordinates x))
    (floor Δ : ℝ) (hlower : ∀ z,floor≤f z) (hgap : f 0-floor≤Δ) :
    Nonempty (P.GapCertificate r 0 Δ) := by
  refine ⟨⟨floor,?_,?_⟩⟩
  · intro x
    rw [hmean]
    exact hlower _
  · rw [hmean,map_zero]
    exact hgap

end Bilevel.EndpointTransportResponse
