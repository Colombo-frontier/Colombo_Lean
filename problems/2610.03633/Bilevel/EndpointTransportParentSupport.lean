import Bilevel.EndpointTransportReleaseSupport
import Bilevel.EndpointTransportNormalKnown
import Bilevel.EndpointTransportCarriers

/-! Full heterogeneous support of the actual last ordinary carrier. Its
parent frontier cancels against the actual flat physical child releases;
the physical derivative includes every terminal release contribution. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.EndpointTransportResponse
open EndpointTransportMatrix ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry PartialLegendre

theorem lastParentCarrier_support {m n D j : ℕ} (hj : j<m) (Q : Rotations n D)
    (N : Node (Block D)) (kids : Fin (N.n+1) → Node (Block D))
    (W : Fin m → Submodule ℝ (Block D)) (Z : Index n → Submodule ℝ (Block D))
    (x : HybridTangent (Blocks m (Block D)) n D) (r : ℕ)
    (hparent : BlindNode W x.fst ⟨j,hj⟩ N r) (rc : Fin (N.n+1) → ℕ)
    (hh : ∀ i,0<(kids i).width) (hR : ∀ i,0<(kids i).radius)
    (hhp : ∀ i,0<(kids i).parentWidth) (hw : ∀ i,(kids i).width≤(kids i).parentWidth)
    (ht : ∀ i,∀ k : Fin ((kids i).n+1),k.val<rc i →
      Q (Fin.last (n+1)) ((kids i).frame (basis k))∈Z (Fin.last (n+1)))
    (hp : ∀ i,∀ k : Fin ((kids i).n+1),rc i≤k.val →
      (gamma n*(kids i).radius)*‖(Z (Fin.last (n+1))).orthogonalProjection
        (Q (Fin.last (n+1)) ((kids i).frame (basis k)))‖≤(kids i).width/8)
    (hY : x.snd∈knownSpace Z) (hfuture : ∀ i,r≤ i.val → rc i≤(kids i).n) :
    gradient (lastParentCarrier m j N kids jointFstLinear jointSndLinear Q) x∈physicalTangentKnown W Z := by
  apply (gradient_physicalTangentKnown_iff W Z x
    (lastParentCarrier_contDiff m j N kids jointFstLinear jointSndLinear Q)).mpr
  let q : Fin (N.n+1) → ℝ := fun i => physicalRelease Q (kids i) x.snd
  have hq : ∀ i,r≤ i.val → q i=0 := fun i hi =>
    (physical_release_flat_on_product Q (kids i) (hh i) (hR i) (hhp i) (hw i)
      (rc i) (hfuture i hi) Z (hp i) x.snd hY).1
  constructor
  · have he : (fun u => lastParentCarrier m j N kids jointFstLinear jointSndLinear Q (pack u x.snd))=
        N.closed q ∘ block m j := by
      funext u
      simp only [lastParentCarrier,physicalReleaseCorrection,jointH,jointResidual,Node.closed,
        Function.comp_apply,mul_sub,mul_one,Finset.sum_sub_distrib]
      change N.H (block m j u)+(∑ i : Fin (N.n+1),N.residual i (block m j u)*q i-
        ∑ i : Fin (N.n+1),N.residual i (block m j u))=_
      ring
    rw [he]
    have hclosed : ContDiff ℝ 3 (N.closed q) := by
      rw [Node.closed_formula]
      exact (closedCarrier_contDiff _ _ _ _ _ _ _ _ q).comp (N.coordinates_contDiff 3)
    exact block_composition_gradient_mem W x.fst ⟨j,hj⟩ hclosed
      (N.closed_gradient_mem r hparent.width_pos hparent.radius_pos q hq _ _
        hparent.query_mem hparent.columns_mem hparent.blind)
  · change gradient (fun Y => jointH m j N x.fst+
      ∑ i : Fin (N.n+1),jointResidual m j N i x.fst*(physicalRelease Q (kids i) Y-1)) x.snd∈knownSpace Z
    apply gradient_add_mem (knownSpace Z) contDiff_const
      (ContDiff.sum (fun i _ => contDiff_const.mul ((physicalRelease_contDiff Q (kids i) 3).sub contDiff_const)))
      x.snd (gradient_const_mem (knownSpace Z) _ x.snd)
    apply gradient_sum_mem Finset.univ (knownSpace Z) _
      (fun i => contDiff_const.mul ((physicalRelease_contDiff Q (kids i) 3).sub contDiff_const))
    intro i _
    apply gradient_mul_mem (knownSpace Z) contDiff_const ((physicalRelease_contDiff Q (kids i) 3).sub contDiff_const)
      x.snd (gradient_const_mem (knownSpace Z) _ x.snd)
    exact gradient_sub_const_mem (knownSpace Z) (physicalRelease_contDiff Q (kids i) 3) x.snd 1
      (physical_release_support_on_product Q (kids i) (hh i) (hR i) (hhp i) (hw i) (rc i) Z (ht i) (hp i) x.snd hY)

end Bilevel.EndpointTransportResponse
