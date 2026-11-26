import Bilevel.EndpointTransportVirtualUpperBorel
import Bilevel.TransportVirtualBatchExact

/-! Exact full upper/lower reply once the two prebatch source identities
are certified. The lower physical Hessian still uses exactly one batch. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry PartialLegendre ChiBoundedChain ChiRecursive ChiCarrier ChiExtension
  TransportHierarchy TransportRound TransportNetwork
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem physicalPrefixJointReply_eq_actual {J n D s a p : ℕ}
    (M : Node E) (ν : ℝ) (G : Geometry (Block D)) (P : ChiFine.Parameters)
    (index radialIndex : Fin J → Fin s) (fineIndex : Fin s)
    (ρ R : ℕ → ℝ) (dn : ℝ) (b : Normals s)
    (rM : ℕ → ℕ) (r rs : ℕ → ℕ → List ℕ → ℕ)
    (data : PhysicalPrefixState M G n)
    (f F : HybridQuery E (Blocks J (Block D)) (Normals s) n D → ℝ)
    (K C : NNReal) (hK : K<1) (hC : C<1)
    (hG : LipschitzWith K (gradient (statePhysicalExtension M G P index radialIndex fineIndex ρ R dn rM r rs data)))
    (hF : LipschitzWith C (gradient F)) (hP : ∀ w,HasGradientAt F (gradient F w) w)
    (m δ c₀ cend : ℝ) (sample : Latent (n+1) D)
    (g : Generators (n+1) D a) (q : Queries (n+1) D p) (i : Fin p)
    (w : HybridQuery E (Blocks J (Block D)) (Normals s) n D)
    (hq : physical (fun v => q v i)=w.snd.fst.snd)
    (hu : gradient (statePhysicalUpper M ν G (ρ 0) (R 0) b rM r data) w=gradient f w)
    (hl : jointGradient hF hC w=jointGradient hG hK w) :
    physicalPrefixJointReply (a:=a) M ν G P index radialIndex fineIndex ρ R dn b rM r rs m δ c₀ cend i
      ((data,w),(q,batch (augment g q) sample))=
      (gradient f w,gradient (hybridLower hF hC F m
        (ChiHybrid.correction (hybridHessian m δ (physicalRotations sample)) m)
        (hybridCoupling c₀ cend (physicalRotations sample))) w) := by
  unfold physicalPrefixJointReply virtualJointReply
  apply Prod.ext
  · exact hu
  · exact virtualHybridReply_eq_actual_of_jointGradient
      (fun data => gradient (statePhysicalExtension M G P index radialIndex fineIndex ρ R dn rM r rs data))
      data hK hG F hC hF hP m δ c₀ cend sample g q i w hq hl

end Bilevel.EndpointTransportResponse
