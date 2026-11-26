import Bilevel.EndpointTransportHybridCoordinates

/-! No gradient loss is incurred by the finite product regrouping. These
identities transfer the original source barrier and gap to the actual
heterogeneous hybrid mean after its exact trace has been established. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry ChiRecursive ChiCarrier ChiOuter

theorem gradient_norm_comp_isometryEquiv
    {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (A : X ≃ₗᵢ[ℝ] Y) (F : Y → ℝ) (x : X) (hF : DifferentiableAt ℝ F (A x)) :
    ‖gradient (fun z => F (A z)) x‖=‖gradient F (A x)‖ := by
  have hd := hF.hasGradientAt.hasFDerivAt.comp x A.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt
  have hg : HasGradientAt (fun z => F (A z)) (A.symm (gradient F (A x))) x := by
    apply hasGradientAt_iff_hasFDerivAt.mpr
    convert hd using 1
    ext z
    change ⟪A.symm (gradient F (A x)),z⟫=⟪gradient F (A x),A z⟫
    rw [← A.inner_map_map,A.apply_symm_apply]
  rw [hg.gradient]
  exact A.symm.norm_map _

variable {E V : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

theorem source_hybrid_gradient_norm {D J n : ℕ} {μ Lf Lg Cf ρg κ : ℝ}
    (M : Node E) (ν : ℝ) (G : Geometry (Block D)) (ρ R : ℕ → ℝ)
    (Pr : Model.Primitive (X:=HybridOuter E (Blocks J (Block D)) D)
      (Y:=HybridVariables (Blocks J (Block D)) V n D) μ Lf Lg Cf ρg)
    (r : Pr.Response)
    (hmean : ∀ x,Pr.hyperobjective r x=jointOuter (J+1) M ν G ρ R J
      (EndpointTransportNormalization.gain κ) (sourceCoordinates J D x))
    (x : HybridOuter E (Blocks J (Block D)) D) :
    ‖gradient (Pr.hyperobjective r) x‖=
      ‖gradient (jointOuter (J+1) M ν G ρ R J (EndpointTransportNormalization.gain κ)) (sourceCoordinates J D x)‖ := by
  rw [show Pr.hyperobjective r=(fun z => jointOuter (J+1) M ν G ρ R J
    (EndpointTransportNormalization.gain κ) (sourceCoordinates J D z)) from funext hmean]
  have hdiff := (jointOuter_contDiff (J+1) M ν G ρ R J (EndpointTransportNormalization.gain κ) 1).differentiable
    (by norm_num)
  have hh := gradient_norm_comp_isometryEquiv (sourceCoordinatesEquiv (E:=E) J D)
    (jointOuter (J+1) M ν G ρ R J (EndpointTransportNormalization.gain κ)) x (hdiff _)
  simpa only [sourceCoordinatesEquiv,LinearIsometryEquiv.coe_ofSurjective] using hh

theorem source_hybrid_gap_transfer {D J n : ℕ} {μ Lf Lg Cf ρg : ℝ}
    (Pr : Model.Primitive (X:=HybridOuter E (Blocks J (Block D)) D)
      (Y:=HybridVariables (Blocks J (Block D)) V n D) μ Lf Lg Cf ρg)
    (r : Pr.Response) (F : Joint E (Blocks (J+1) (Block D)) → ℝ)
    (hmean : ∀ x,Pr.hyperobjective r x=F (sourceCoordinates J D x))
    (floor Δ : ℝ) (hlower : ∀ z,floor≤F z) (hgap : F 0-floor≤Δ) :
    Nonempty (Pr.GapCertificate r 0 Δ) := by
  refine ⟨⟨floor,?_,?_⟩⟩
  · intro x
    rw [hmean]
    exact hlower _
  · rw [hmean,map_zero]
    exact hgap

end Bilevel.EndpointTransportResponse
