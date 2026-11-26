import Bilevel.EndpointTransportCompletionNodes
import Bilevel.EndpointTransportNormalExtension

/-! The entire public radial sum is unchanged under the actual isometric
completion, including the final physically rescaled channel. -/
noncomputable section
namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry ChiCarrier ChiExtension
set_option autoImplicit false
set_option maxHeartbeats 1200000
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem publicRadialProjection_completion_norm {J n D D' : ℕ}
    (M : E →ₗᵢ[ℝ] F) (I : Block D →ₗᵢ[ℝ] Block D') (i : Fin J) (x : PhysicalBase E J n D) :
    ‖publicRadialProjection n D' i (completionBaseMap M I x)‖=‖publicRadialProjection n D i x‖ := by
  unfold publicRadialProjection
  split_ifs with hi
  · rw [ordinaryRadialProjection_norm,ordinaryRadialProjection_norm]
    change ‖I (x.snd.fst ⟨i.val+1,hi⟩)‖=_
    exact I.norm_map _
  · rw [physicalRadialProjection_norm,physicalRadialProjection_norm]
    change ‖physicalMap I x.snd.snd‖=_
    exact (physicalMap I).norm_map _

theorem radial_eq_of_norm {A B : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
    [NormedAddCommGroup B] [InnerProductSpace ℝ B] (u : A) (v : B) (h : ‖u‖=‖v‖) (ν R dn t : ℝ) :
    PublicRadialExtension.radial ν R dn (pack u t)=PublicRadialExtension.radial ν R dn (pack v t) := by
  simp only [PublicRadialExtension.radial,PublicRadialExtension.potential,
    PublicRadialExtension.normalDirection_inner,RadialWrapper.bowl,norm_pack,h]

theorem publicRadialSum_completion {J n D D' s : ℕ}
    (M : E →ₗᵢ[ℝ] F) (I : Block D →ₗᵢ[ℝ] Block D')
    (index : Fin J → Fin s) (ρ R : ℕ → ℝ) (dn : ℝ) (z : Full (PhysicalBase E J n D) s) :
    radialSum index (publicRadialProjection n D') (publicRadialProjection_norm_le n D')
      (publicRadialCurvature n ρ) (publicRadialRadius n R) dn (completionFullMap s M I z)=
      radialSum index (publicRadialProjection n D) (publicRadialProjection_norm_le n D)
        (publicRadialCurvature n ρ) (publicRadialRadius n R) dn z := by
  unfold radialSum
  apply Finset.sum_congr rfl
  intro i _
  change PublicRadialExtension.radial _ _ _
    (pack (publicRadialProjection n D' i (completionBaseMap M I z.fst)) (z.snd (index i)))=
      PublicRadialExtension.radial _ _ _ (pack (publicRadialProjection n D i z.fst) (z.snd (index i)))
  exact radial_eq_of_norm _ _ (publicRadialProjection_completion_norm M I i z.fst) _ _ _ _

end Bilevel.EndpointTransportResponse
