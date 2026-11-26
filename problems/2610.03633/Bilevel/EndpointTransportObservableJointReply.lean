import Bilevel.EndpointTransportObservableReply
import Bilevel.EndpointTransportObservableUpper
import Bilevel.EndpointTransportVirtualJointExact

/-! The complete original physical SFO pair from one observable prebatch
certificate. Both nonlinear identities are discharged from its coordinate
and projection bounds, before the single frozen Hessian batch is read. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry PartialLegendre ChiBoundedChain ChiRecursive ChiCarrier ChiPrefixEvaluation ChiExtension
  TransportHierarchy TransportRound TransportNetwork
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem observable_physical_joint_reply {J n D s a p : ℕ}
    (M : Node E) (ν : ℝ) (G : Geometry (Block D)) (P : ChiFine.Parameters) (hJ : 0<J)
    (index radialIndex : Fin J → Fin s) (fineIndex : Fin s)
    (ρ R : ℕ → ℝ) (dn : ℝ) (b : Normals s) (hR : ∀ i : Fin J,0<R (i.val+1))
    (rM : ℕ → ℕ) (r rs : ℕ → ℕ → List ℕ → ℕ) (data : PhysicalPrefixState M G n)
    (sample : Latent (n+1) D)
    (W : Fin J → Submodule ℝ (Block D)) (Z : EndpointTransportMatrix.Index n → Submodule ℝ (Block D))
    (hcert : ObservablePhysicalPrefixCertificate (physicalRotations sample) M G P W Z
      (rM data.1) (r data.1) (rs data.1) data.2.1 data.2.2.1 data.2.2.2.1 data.2.2.2.2)
    (hmw : 0<M.width) (hmR : 0<M.radius)
    (hmfuture : ∀ i : Fin (M.n+1),rM data.1 ≤ i.val → r data.1 0 [i.val]≤(G 0 [i.val]).n)
    (K C : NNReal) (hK : K<1) (hC : C<1)
    (hcore : ContDiff ℝ 3 (physicalHierarchyExtension (physicalRotations sample) M G P J s index radialIndex fineIndex ρ R dn))
    (hH : ∀ z,‖iteratedFDeriv ℝ 2
      (physicalHierarchyExtension (physicalRotations sample) M G P J s index radialIndex fineIndex ρ R dn) z‖≤(C:ℝ))
    (hF : LipschitzWith C (gradient (physicalExtension (U:=Blocks J (Block D)) (D:=D)
      (physicalHierarchyExtension (physicalRotations sample) M G P J s index radialIndex fineIndex ρ R dn))))
    (hG : LipschitzWith K (gradient (statePhysicalExtension M G P index radialIndex fineIndex ρ R dn rM r rs data)))
    (ξ : ℝ) (hξ : 0<ξ) (hξM : ξ≤M.width/16) (hξG : ∀ k A,k≤J → ξ≤(G k A).width/16)
    (m δ c₀ cend : ℝ) (g : Generators (n+1) D a) (q : Queries (n+1) D p) (i : Fin p)
    (w : HybridQuery E (Blocks J (Block D)) (Normals s) n D)
    (hq : physical (fun v => q v i)=w.snd.fst.snd)
    (hy : w.snd∈physicalNormalKnown W Z s)
    (hmb : ∀ k : Fin (M.n+1),rM data.1≤k.val → |M.coordinates w.fst.fst.fst k|≤M.width/8) :
    physicalPrefixJointReply (a:=a) M ν G P index radialIndex fineIndex ρ R dn b rM r rs m δ c₀ cend i
      ((data,w),(q,batch (augment g q) sample))=
      (gradient (physicalUpper (U:=Blocks J (Block D)) (D:=D)
          (physicalUpperBase J (physicalRotations sample) M ν G J (ρ 0) (R 0)) b) w,
        gradient (hybridLower hF hC
          (physicalExtension (U:=Blocks J (Block D)) (D:=D)
            (physicalHierarchyExtension (physicalRotations sample) M G P J s index radialIndex fineIndex ρ R dn))
          m (ChiHybrid.correction (hybridHessian m δ (physicalRotations sample)) m)
          (hybridCoupling c₀ cend (physicalRotations sample))) w) := by
  have hu := (physicalUpper_gradient_eq_observable_prefix (physicalRotations sample) M ν G P hJ
    (ρ 0) (R 0) b W Z (rM data.1) (r data.1) (rs data.1)
    data.2.1 data.2.2.1 data.2.2.2.1 data.2.2.2.2 hcert hmw hmR hmfuture
    ξ hξ hξM hξG w.fst w.snd hy hmb).symm
  have hl := (physicalHierarchy_observable_inverse_reply_eq_prefix (physicalRotations sample) M G P
    index radialIndex fineIndex ρ R dn hR W Z (rM data.1) (r data.1) (rs data.1)
    data.2.1 data.2.2.1 data.2.2.2.1 data.2.2.2.2 hcert hmw hmR C hC hH hF
    ξ hξ hξM hξG w.fst w.snd hy hmb K hK hG).2
  exact physicalPrefixJointReply_eq_actual M ν G P index radialIndex fineIndex ρ R dn b rM r rs data
    _ _ K C hK hC hG hF
    (fun z => ((physicalExtension_contDiff hcore).differentiable (by norm_num) z).hasGradientAt)
    m δ c₀ cend sample g q i w hq hu hl

end Bilevel.EndpointTransportResponse
