import Bilevel.EndpointTransportNormalKnown
import Bilevel.EndpointTransportRadialChannels
import Bilevel.ChiHierarchyRadialLocality

/-! Every actual public radial normal channel preserves the heterogeneous
known tangent space, including the full gamma-scaled physical block. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators
namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry PartialLegendre ChiCarrier ChiExtension ChiOuter PublicRadialExtension
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem ordinary_radial_normal_value {J n D : ℕ} (i : Fin J) (ν R dn τ : ℝ)
    (hR : 0<R) (a : E) (z : HybridTangent (Blocks J (Block D)) n D) :
    radial ν R dn (pack (ordinaryRadialProjection i (pack a z)) τ)=
      radial ν R dn (pack (z.fst i) τ) := by
  rw [radial_formula ν R dn hR,radial_formula ν R dn hR,ordinaryRadialProjection_norm]
  rfl

theorem physical_radial_normal_value {J n D : ℕ} (ν R dn τ : ℝ)
    (hR : 0<R) (a : E) (z : HybridTangent (Blocks J (Block D)) n D) :
    radial ν R dn (pack (physicalRadialProjection J n D (pack a z)) τ)=
      radial ν R dn (pack z.snd τ) := by
  rw [radial_formula ν R dn hR,radial_formula ν R dn hR,physicalRadialProjection_norm]
  rfl

theorem ordinary_radial_normal_support {J n D : ℕ} (i : Fin J) (ν R dn τ : ℝ)
    (hR : 0<R) (a : E) (z : HybridTangent (Blocks J (Block D)) n D)
    (W : Fin J → Submodule ℝ (Block D)) (Z : EndpointTransportMatrix.Index n → Submodule ℝ (Block D))
    (hz : z∈physicalTangentKnown W Z) :
    gradient (fun y => radial ν R dn (pack (ordinaryRadialProjection i (pack a y)) τ)) z∈
      physicalTangentKnown W Z := by
  rw [show (fun y => radial ν R dn (pack (ordinaryRadialProjection i (pack a y)) τ))=
      (fun y : HybridTangent (Blocks J (Block D)) n D => radial ν R dn (pack (y.fst i) τ)) from
    funext (ordinary_radial_normal_value i ν R dn τ hR a)]
  rw [show (fun y : HybridTangent (Blocks J (Block D)) n D => radial ν R dn (pack (y.fst i) τ))=
      (((fun u : Block D => radial ν R dn (pack u τ)) ∘ block (E:=Block D) J i.val) ∘
        jointFstLinear (A:=Blocks J (Block D)) (B:=Physical n D)) by
    funext y
    simp only [Function.comp_apply,block,dif_pos i.isLt,PiLp.proj_apply]
    rfl]
  apply fst_composition_gradient_mem (knownSpace W) (knownSpace Z)
    ((radial_inner_contDiff ν R dn τ).comp (block (E:=Block D) J i.val).contDiff) z
  apply block_composition_gradient_mem W z.fst i (radial_inner_contDiff ν R dn τ)
  rw [radial_inner_gradient ν R dn τ hR]
  exact (W i).smul_mem _ (((mem_physicalTangentKnown W Z z).mp hz).1 i)

theorem physical_radial_normal_support {J n D : ℕ} (ν R dn τ : ℝ)
    (hR : 0<R) (a : E) (z : HybridTangent (Blocks J (Block D)) n D)
    (W : Fin J → Submodule ℝ (Block D)) (Z : EndpointTransportMatrix.Index n → Submodule ℝ (Block D))
    (hz : z∈physicalTangentKnown W Z) :
    gradient (fun y => radial ν R dn (pack (physicalRadialProjection J n D (pack a y)) τ)) z∈
      physicalTangentKnown W Z := by
  rw [show (fun y => radial ν R dn (pack (physicalRadialProjection J n D (pack a y)) τ))=
      (fun y : HybridTangent (Blocks J (Block D)) n D => radial ν R dn (pack y.snd τ)) from
    funext (physical_radial_normal_value ν R dn τ hR a)]
  change gradient ((fun Y : Physical n D => radial ν R dn (pack Y τ)) ∘
    jointSndLinear (A:=Blocks J (Block D)) (B:=Physical n D)) z∈physicalTangentKnown W Z
  apply snd_composition_gradient_mem (knownSpace W) (knownSpace Z) (radial_inner_contDiff ν R dn τ) z
  rw [radial_inner_gradient ν R dn τ hR]
  exact (knownSpace Z).smul_mem _ ((mem_physicalTangentKnown W Z z).mp hz).2

theorem public_radial_normal_support {J n D : ℕ} (i : Fin J) (ν R dn τ : ℝ)
    (hR : 0<R) (a : E) (z : HybridTangent (Blocks J (Block D)) n D)
    (W : Fin J → Submodule ℝ (Block D)) (Z : EndpointTransportMatrix.Index n → Submodule ℝ (Block D))
    (hz : z∈physicalTangentKnown W Z) :
    gradient (fun y => radial ν R dn (pack (publicRadialProjection n D i (pack a y)) τ)) z∈
      physicalTangentKnown W Z := by
  unfold publicRadialProjection
  split_ifs with h
  · exact ordinary_radial_normal_support ⟨i.val+1,h⟩ ν R dn τ hR a z W Z hz
  · exact physical_radial_normal_support ν R dn τ hR a z W Z hz

theorem physical_radialSum_support {J n D s : ℕ} (index : Fin J → Fin s) (ρ R : ℕ → ℝ) (dn : ℝ)
    (hR : ∀ i : Fin J,0<R (i.val+1)) (a : E) (z : HybridTangent (Blocks J (Block D)) n D)
    (q : Normals s) (W : Fin J → Submodule ℝ (Block D))
    (Z : EndpointTransportMatrix.Index n → Submodule ℝ (Block D)) (hz : z∈physicalTangentKnown W Z) :
    gradient (fun y => radialSum index (publicRadialProjection (E:=E) n D)
      (publicRadialProjection_norm_le (E:=E) n D) (publicRadialCurvature n ρ) (publicRadialRadius n R) dn
      (pack (pack a y) q)) z∈physicalTangentKnown W Z := by
  change gradient (fun y => ∑ i : Fin J,radial (publicRadialCurvature n ρ i) (publicRadialRadius n R i) dn
    (pack (publicRadialProjection n D i (pack a y)) (q (index i)))) z∈_
  apply gradient_sum_mem Finset.univ (physicalTangentKnown W Z) _
  · intro i
    exact (radial_inner_contDiff (publicRadialCurvature n ρ i) (publicRadialRadius n R i) dn (q (index i))).comp
      ((publicRadialProjection (E:=E) n D i).contDiff.comp
        ((packLinear (X:=E) (Y:=HybridTangent (Blocks J (Block D)) n D)).contDiff.comp
          (contDiff_const.prodMk contDiff_id)))
  · intro i _
    exact public_radial_normal_support i _ _ dn (q (index i)) (publicRadialRadius_pos n R hR i) a z W Z hz

end Bilevel.EndpointTransportResponse
