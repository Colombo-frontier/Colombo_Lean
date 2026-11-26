import Bilevel.EndpointTransportOperator
import Bilevel.ChiQuadraticPrimitive
import Bilevel.ChiCarrierSupportSpace

/-! Actual endpoint coupling and exact response, with the prescribed lower
Primitive budgets. The upper scalar remains an explicit differentiable input;
its split-payload construction is a separate obligation. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Bilevel.EndpointTransportResponse
open EndpointTransportMatrix PrimitiveGeometry PartialLegendre ChiCarrier
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def endpointCoupling {n D : ℕ} (c : ℝ) (Q : Rotations n D) :
    Joint E (Block D) →L[ℝ] Physical n D :=
  c • ((insertion (n+2) (Fin.last (n+1))).toContinuousLinearMap.comp
    ((Q (Fin.last (n+1))).toContinuousLinearMap.comp jointSndLinear))

omit [CompleteSpace E] in
theorem endpointCoupling_apply {n D : ℕ} (c : ℝ) (Q : Rotations n D)
    (x : Joint E (Block D)) :
    endpointCoupling c Q x=c • insertion (n+2) (Fin.last (n+1)) (Q (Fin.last (n+1)) x.snd) := rfl

omit [CompleteSpace E] in
theorem endpointCoupling_norm {n D : ℕ} (c : ℝ) (Q : Rotations n D) :
    ‖(endpointCoupling c Q : Joint E (Block D) →L[ℝ] Physical n D)‖≤|c| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (abs_nonneg c)
  intro x
  rw [endpointCoupling_apply,norm_smul,Real.norm_eq_abs,LinearIsometry.norm_map,LinearIsometryEquiv.norm_map]
  exact mul_le_mul_of_nonneg_left (WithLp.norm_snd_le E x) (abs_nonneg c)

omit [CompleteSpace E] in
theorem endpointCoupling_inner {n D : ℕ} (c : ℝ) (Q : Rotations n D)
    (x : Joint E (Block D)) (Y : Physical n D) :
    ⟪endpointCoupling c Q x,Y⟫=c*⟪Q (Fin.last (n+1)) x.snd,Y (Fin.last (n+1))⟫ := by
  rw [endpointCoupling_apply,real_inner_smul_left,real_inner_comm,
    inner_insertion_right,real_inner_comm]

omit [CompleteSpace E] in
theorem lower_eq_quadratic {n D : ℕ} (δ c : ℝ) (Q : Rotations n D)
    (x : Joint E (Block D)) (Y : Physical n D) :
    ChiQuadratic.lower (physicalHessian δ Q) (endpointCoupling c Q) (pack x Y)=lower δ c Q x.snd Y := by
  change (1/2)*⟪Y,physicalHessian δ Q Y⟫-⟪endpointCoupling c Q x,Y⟫= _
  rw [physicalHessian_quadratic,endpointCoupling_inner,lower_block_formula]
  ring

omit [CompleteSpace E] in
theorem physical_response_equation {n D : ℕ} {δ : ℝ} (hδ : δ≠0) (c : ℝ)
    (Q : Rotations n D) (x : Joint E (Block D)) :
    physicalHessian δ Q (physicalResponse δ c Q x.snd)=endpointCoupling c Q x := by
  ext i d
  have hs := congrFun (response_solves_system hδ c Q x.snd) i
  change hessianAction δ Q (response δ c Q x.snd) i=
    (c*lastUnit n i) • Q i x.snd at hs
  change (hessianAction δ Q (response δ c Q x.snd) i) d=(endpointCoupling c Q x i) d
  rw [hs,endpointCoupling_apply]
  simp only [PiLp.smul_apply,insertion_apply,lastUnit_eq_single,Pi.single_apply,smul_eq_mul]
  split_ifs with he
  · subst i
    simp
  · simp

theorem physicalResponse_zero {n D : ℕ} (δ c : ℝ) (Q : Rotations n D) :
    physicalResponse δ c Q 0=0 := by
  ext i d
  simp [physicalResponse,response]

theorem transport_primitive {D : ℕ} {L κ : ℝ} (hL : 0<L) (hκ : 3200≤κ)
    (Q : Rotations (EndpointTransportNormalization.interiors κ) D)
    (f : Joint (Joint E (Block D)) (Physical (EndpointTransportNormalization.interiors κ) D) → ℝ)
    (hf : ContDiff ℝ 3 f)
    (hupper : ∀ x y,‖gradient (fun v => f (pack x v)) y‖≤L)
    (hjet : ∀ z,‖iteratedFDeriv ℝ 2 f z‖≤L) :
    ∃ P : Model.Primitive (X:=Joint E (Block D))
      (Y:=Physical (EndpointTransportNormalization.interiors κ) D) (L/κ) L L L 0,
      (∀ x y,P.f x y=f (pack x y)) ∧
      (∀ x y,P.g x y=lower (L/16) (L/4) Q x.snd y) ∧
      (∀ x y,P.gyy x y=physicalHessian (L/16) Q) ∧
      ∃ r : P.Response,r.y 0=0 ∧
        (∀ x,r.y x=physicalResponse (L/16) (L/4) Q x.snd) ∧
        (∀ x,P.hyperobjective r x=f (pack x (physicalResponse (L/16) (L/4) Q x.snd))) ∧
        (∀ x y,P.IsLowerSolution x y ↔ y=physicalResponse (L/16) (L/4) Q x.snd) := by
  have hκp : 0<κ := by linarith only [hκ]
  have hμ : 0<L/κ := div_pos hL hκp
  have hnorm := normalized_physicalHessian hL.le hκ Q
  have hcoerce (y : Physical (EndpointTransportNormalization.interiors κ) D) :
      (L/κ)*‖y‖^2≤⟪y,physicalHessian (L/16) Q y⟫ := by
    have hh := hnorm.2 y
    have hn := mul_nonneg hμ.le (sq_nonneg ‖y‖)
    nlinarith only [hh,hn]
  have hc := endpointCoupling_norm (E:=E) (L/4) Q
  rw [abs_of_pos (by positivity : 0<L/4)] at hc
  have hb : ‖physicalHessian (L/16) Q‖+‖(endpointCoupling (L/4) Q : Joint E (Block D) →L[ℝ] _)‖≤L := by
    linarith only [hnorm.1,hc,hL]
  obtain ⟨P,hfP,hgP,_hgy,hyy,_hxy,r,hr,hm,hu⟩ := ChiQuadratic.quadratic_primitive f hf
    (physicalHessian (L/16) Q) (endpointCoupling (L/4) Q) (physicalHessian_symmetric _ Q)
    (L/κ) L L L hμ hL.le hL.le hcoerce hb hupper hjet
    (fun x => physicalResponse (L/16) (L/4) Q x.snd)
    (physical_response_equation (by positivity : L/16≠0) (L/4) Q)
  refine ⟨P,hfP,?_,hyy,r,?_,hr,hm,hu⟩
  · intro x y
    exact (hgP x y).trans (lower_eq_quadratic _ _ Q x y)
  · rw [hr]
    exact physicalResponse_zero _ _ Q

end Bilevel.EndpointTransportResponse
