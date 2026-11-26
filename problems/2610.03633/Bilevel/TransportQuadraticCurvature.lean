import Bilevel.EndpointTransportAffineResponse
import Bilevel.ChiAffineGraphCurvature
import Bilevel.ResponseExistence

/-! The exact quadratic family's actual affine response has curvature
at most 4 L kappa^2, independently of its declared variation budget. -/
noncomputable section
namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry PartialLegendre
set_option autoImplicit false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem physical_affine_curvature {n D : ℕ} {L κ ρg : ℝ} (hL : 0<L) (hκ : 1≤κ)
    (P : Model.Primitive (X:=Joint E (Block D)) (Y:=Physical n D) (L/κ) L L L ρg)
    (f : Joint (Joint E (Block D)) (Physical n D) → ℝ) (hf : Differentiable ℝ f)
    (hPf : ∀ x y,P.f x y=f (pack x y)) (δ c : ℝ) (Q : Rotations n D)
    (r : P.Response) (hr : ∀ x,r.y x=physicalResponse δ c Q x.snd) :
    LipschitzWith ⟨4*L*κ^2,by positivity⟩ (gradient (P.hyperobjective r)) := by
  let B : Joint E (Block D) →L[ℝ] Physical n D := (physicalResponseCLM δ c Q).comp jointSndLinear
  let A : Joint E (Block D) →L[ℝ] Joint (Joint E (Block D)) (Physical n D) :=
    packLinear.comp ((ContinuousLinearMap.id ℝ (Joint E (Block D))).prod B)
  have hκ0 : 0<κ := zero_lt_one.trans_le hκ
  have hratio : L/(L/κ)=κ := by field_simp
  have hr0 : r.y 0=0 := by rw [hr];exact physicalResponse_zero δ c Q
  have hB (x : Joint E (Block D)) : ‖B x‖≤κ*‖x‖ := by
    have hh := P.response_distance_bound r x 0
    rw [hr x,hr0,sub_zero,sub_zero,hratio] at hh
    exact hh
  have hA : ‖A‖≤2*κ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro x
    change ‖pack x (B x)‖≤(2*κ)*‖x‖
    have hh := (norm_pack_le_add x (B x)).trans (add_le_add_left (hB x) ‖x‖)
    nlinarith only [hh,hκ,norm_nonneg x]
  have hgraph (x : Joint E (Block D)) : A x=pack x (r.y x) := by
    rw [hr]
    rfl
  have hh := ChiPrimitive.affine_graph_gradient_lipschitz P f hf hPf r A hgraph (by positivity : 0≤2*κ) hA
  convert hh using 1
  congr 1
  ring

end Bilevel.EndpointTransportResponse
