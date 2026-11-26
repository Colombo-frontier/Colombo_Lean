import Bilevel.TransportVirtualHybridReply

/-! Connect a certified prebatch nonlinear reply equality to the literal
original lower gradient using the same single frozen transport batch. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
namespace Bilevel.TransportHierarchy
open PrimitiveGeometry PartialLegendre EndpointTransportResponse TransportRound TransportNetwork
variable {A E U V : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

theorem virtualHybridReply_eq_actual_of_jointGradient {n D a p : ℕ}
    (G : A → HybridQuery E U V n D → HybridQuery E U V n D) (parameter : A)
    {K : NNReal} (hK : K<1) (hG : LipschitzWith K (G parameter))
    (P : HybridQuery E U V n D → ℝ)
    {C : NNReal} (hC : C<1) (hF : LipschitzWith C (gradient P))
    (hP : ∀ w,HasGradientAt P (gradient P w) w)
    (m δ c₀ cend : ℝ) (z : Latent (n+1) D)
    (g : Generators (n+1) D a) (q : Queries (n+1) D p) (i : Fin p)
    (w : HybridQuery E U V n D) (hq : physical (fun v => q v i)=w.snd.fst.snd)
    (he : jointGradient hF hC w=jointGradient hG hK w) :
    virtualHybridReply G m δ c₀ cend i ((parameter,w),(q,batch (augment g q) z))=
      gradient (hybridLower hF hC P m
        (ChiHybrid.correction (hybridHessian m δ (physicalRotations z)) m)
        (hybridCoupling c₀ cend (physicalRotations z))) w := by
  rw [virtualHybridReply,ParametricPartialConjugate.gradientReply_eq_jointGradient G parameter hK hG,← he]
  exact (hybridLower_gradient_from_batch m δ c₀ cend z P hF hC hP g q i w hq).symm

end Bilevel.TransportHierarchy
