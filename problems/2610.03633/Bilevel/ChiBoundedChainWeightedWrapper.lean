import Bilevel.ChiBoundedChainWeightedGeometry

/-! Actual weighted local objective, radial coefficient and projected gradient.
The interior margin still records its coefficient bounds as explicit premises;
the construction-specific global budgets are separate obligations. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.ChiBoundedChain
open RadialWrapper
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem frame_adjoint_apply {n : ℕ} (U : Space n →ₗᵢ[ℝ] E) (v : Space n) :
    U.toContinuousLinearMap.adjoint (U v)=v := by
  have he := U.toContinuousLinearMap.norm_map_iff_adjoint_comp_self.mp U.norm_map
  have hh := congrArg (fun f : Space n →L[ℝ] Space n => f v) he
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.one_apply,
    LinearIsometry.coe_toContinuousLinearMap] using hh

theorem frame_adjoint_norm_le {n : ℕ} (U : Space n →ₗᵢ[ℝ] E) (v : E) :
    ‖U.toContinuousLinearMap.adjoint v‖≤‖v‖ := by
  have hn : ‖U.toContinuousLinearMap.adjoint‖≤1 := by
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact U.norm_toContinuousLinearMap_le
  exact (U.toContinuousLinearMap.adjoint.le_opNorm v).trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hn (norm_nonneg v))

def radialCoefficient {n : ℕ} (ρ radius : ℝ) (U : Space n →ₗᵢ[ℝ] E)
    (u : E) (p : Space n) : ℝ := ρ-scale radius u^2/radius^2*⟪u,U p⟫

theorem radialCoefficient_source_formula {n : ℕ} (ρ radius : ℝ) (U : Space n →ₗᵢ[ℝ] E)
    (u : E) (p : Space n) : radialCoefficient ρ radius U u p=
      ρ-scale radius u*⟪WrappedChain.coordinates n radius U u,p⟫/radius^2 := by
  have hi : ⟪WrappedChain.coordinates n radius U u,p⟫=scale radius u*⟪u,U p⟫ := by
    change ⟪U.toContinuousLinearMap.adjoint (compress radius u),p⟫=_
    rw [ContinuousLinearMap.adjoint_inner_left,compress,real_inner_smul_left]
    rfl
  rw [hi]
  unfold radialCoefficient
  ring

theorem projected_wrappedGradient {n : ℕ} (ρ radius : ℝ) (U : Space n →ₗᵢ[ℝ] E)
    (u : E) (p : Space n) :
    U.toContinuousLinearMap.adjoint (wrappedGradient ρ radius u (U p))=
      radialCoefficient ρ radius U u p • WrappedChain.coordinates n radius U u+
        scale radius u • p := by
  simp only [wrappedGradient,map_add,map_smul,frame_adjoint_apply,
    WrappedChain.coordinates,compress,radialCoefficient,smul_smul]
  module

def weightedLocal (n : ℕ) (ℓ h A ν g hp T w Rp ρ radius : ℝ)
    (U : Space n →ₗᵢ[ℝ] E) : E → ℝ :=
  wrapped ρ radius (weightedLatent n ℓ h A ν g hp T w Rp) U.toContinuousLinearMap.adjoint

theorem weightedLocal_formula (n : ℕ) (ℓ h A ν g hp T w Rp ρ radius : ℝ)
    (U : Space n →ₗᵢ[ℝ] E) (u : E) :
    weightedLocal n ℓ h A ν g hp T w Rp ρ radius U u=
      bowl ρ radius u+w*payload n ℓ h A ν g hp T (WrappedChain.coordinates n radius U u)+
        Rp*releaseGate (WrappedChain.coordinates n radius U u (Fin.last n)/hp) := by
  simp only [weightedLocal,wrapped,weightedLatent,WrappedChain.coordinates]
  ring

theorem weightedLocal_hasGradientAt (n : ℕ) (ℓ h A ν g hp T w Rp ρ radius : ℝ)
    (hR : 0<radius) (U : Space n →ₗᵢ[ℝ] E) (u : E) :
    HasGradientAt (weightedLocal n ℓ h A ν g hp T w Rp ρ radius U)
      (wrappedGradient ρ radius u (U (gradient (weightedLatent n ℓ h A ν g hp T w Rp)
        (WrappedChain.coordinates n radius U u)))) u := by
  have hh := wrapped_hasGradientAt ρ radius hR (weightedLatent n ℓ h A ν g hp T w Rp)
    U.toContinuousLinearMap.adjoint u _
    (weightedLatent_hasGradientAt n ℓ h A ν g hp T w Rp
      (WrappedChain.coordinates n radius U u)).differentiableAt.hasGradientAt
  simpa only [weightedLocal,ContinuousLinearMap.adjoint_adjoint,
    LinearIsometry.coe_toContinuousLinearMap] using hh

theorem weightedLocal_projected_gradient (n : ℕ) (ℓ h A ν g hp T w Rp ρ radius : ℝ)
    (hR : 0<radius) (U : Space n →ₗᵢ[ℝ] E) (u : E) :
    U.toContinuousLinearMap.adjoint (gradient (weightedLocal n ℓ h A ν g hp T w Rp ρ radius U) u)=
      radialCoefficient ρ radius U u (gradient (weightedLatent n ℓ h A ν g hp T w Rp)
        (WrappedChain.coordinates n radius U u)) • WrappedChain.coordinates n radius U u+
        scale radius u • gradient (weightedLatent n ℓ h A ν g hp T w Rp)
          (WrappedChain.coordinates n radius U u) := by
  rw [(weightedLocal_hasGradientAt n ℓ h A ν g hp T w Rp ρ radius hR U u).gradient,
    projected_wrappedGradient]

theorem weightedLocal_interior_global_margin (n : ℕ) (ℓ h A ν g hp T w b Rp radius K : ℝ)
    (hℓ : 0≤ℓ) (hA : 3≤A) (hν : 0<ν) (hg : g=ℓ*h) (hh : 0<h) (hhp : 0<hp)
    (hT : 0<T) (hb : 0≤b) (hbw : b≤w) (hRp : Rp≤0) (hK : 1≤K)
    (hTscale : ν*T=K*g) (hR : 0<radius) (U : Space n →ₗᵢ[ℝ] E) (u : E)
    (hu : ‖u‖≤radius)
    (hclow : b*ν/2≤radialCoefficient (b*ν) radius U u
      (gradient (weightedLatent n ℓ h A ν g hp T w Rp) (WrappedChain.coordinates n radius U u)))
    (hcup : radialCoefficient (b*ν) radius U u
      (gradient (weightedLatent n ℓ h A ν g hp T w Rp) (WrappedChain.coordinates n radius U u))≤5*b*ν/4)
    (hwidth : radialCoefficient (b*ν) radius U u
      (gradient (weightedLatent n ℓ h A ν g hp T w Rp) (WrappedChain.coordinates n radius U u))*h≤w*g/6)
    (hQ : releaseGate (WrappedChain.coordinates n radius U u (Fin.last n)/hp)<1) :
    b*g/2≤‖gradient (weightedLocal n ℓ h A ν g hp T w Rp (b*ν) radius U) u‖ := by
  have hgeom := weighted_interior_global_margin n ℓ h A ν g hp T w b Rp _ _ K
    hℓ hA hν hg hh hhp hT hb hbw hRp hK hTscale hclow hcup
    (scale_interior_lower radius hR u hu) hwidth (WrappedChain.coordinates n radius U u) hQ
  rw [← weightedLocal_projected_gradient n ℓ h A ν g hp T w Rp (b*ν) radius hR U u] at hgeom
  exact hgeom.trans (frame_adjoint_norm_le U _)

end Bilevel.ChiBoundedChain
