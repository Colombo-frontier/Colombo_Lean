import Bilevel.EndpointTransportHybridCoordinates

/-! A single actual transport hybrid Primitive and its exact original-source
mean. The extension-to-carrier trace and actual upper jets remain explicit
assembly inputs; the inverse, minimizer, and mean identities are proved. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry PartialLegendre ChiRecursive ChiCarrier ChiOuter
variable {E V : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

def hybridUpper {D J n : ℕ} (base : E → HybridTangent (Blocks J (Block D)) n D → ℝ) (b : V)
    (z : Joint (HybridOuter E (Blocks J (Block D)) D) (HybridVariables (Blocks J (Block D)) V n D)) : ℝ :=
  base z.fst.fst.fst z.snd.fst+⟪b,z.snd.snd⟫

theorem source_hybrid_witness_of_trace {D J : ℕ} {L κ ρg : ℝ}
    (hL : 0<L) (hκ : 3200≤κ) (hρg : 0≤ρg)
    (Q : Rotations (EndpointTransportNormalization.interiors κ) D)
    (M : Node E) (ν : ℝ) (G : Geometry (Block D)) (ρ R : ℕ → ℝ)
    (P : Joint (HybridOuter E (Blocks J (Block D)) D)
      (HybridVariables (Blocks J (Block D)) V (EndpointTransportNormalization.interiors κ) D) → ℝ)
    (hP : ContDiff ℝ 3 P) (δ : NNReal)
    (h2 : ∀ z,‖iteratedFDeriv ℝ 2 P z‖≤(δ:ℝ)) (hδ : δ<1) (hsmall : (δ:ℝ)≤1/12)
    (hzero : ∀ x p,P (pack x (pack p (0:V)))=0)
    (h3 : ∀ z,‖iteratedFDeriv ℝ 3 P z‖≤ρg/(3*(3*(L/κ)/2)))
    (base : E → HybridTangent (Blocks J (Block D)) (EndpointTransportNormalization.interiors κ) D → ℝ)
    (b : V) (hf : ContDiff ℝ 3 (hybridUpper base b))
    (hf2 : ∀ z,‖iteratedFDeriv ℝ 2 (hybridUpper base b) z‖≤L)
    (hfy : ∀ x y,‖gradient (fun w => hybridUpper base b (pack x w)) y‖≤L)
    (htrace : ∀ x p,base x.fst.fst p+⟪b,(gradient P (pack x (pack p (0:V)))).snd.snd⟫=
      physicalOuter Q M ν G ρ R J x.fst.fst (padded p.fst) p.snd) :
    ∃ Pr : Model.Primitive (X:=HybridOuter E (Blocks J (Block D)) D)
        (Y:=HybridVariables (Blocks J (Block D)) V (EndpointTransportNormalization.interiors κ) D)
        (L/κ) L L L ρg,
      (∀ x y,Pr.f x y=base x.fst.fst y.fst+⟪b,y.snd⟫) ∧
      (∀ x y,Pr.g x y=sourceHybridLower L κ Q P hP δ h2 hδ (pack x y)) ∧
      ∃ r : Pr.Response,
        (∀ x,r.y x=ChiHybrid.responseOfExtension P (sourceHybridTangent L κ Q) x) ∧
        (∀ x,Pr.hyperobjective r x=jointOuter (J+1) M ν G ρ R J
          (EndpointTransportNormalization.gain κ) (sourceCoordinates J D x)) ∧
        (∀ x y,Pr.IsLowerSolution x y ↔ y=ChiHybrid.responseOfExtension P (sourceHybridTangent L κ Q) x) := by
  obtain ⟨Pr,hfPr,hgPr,r,hr,_hmean,hunique⟩ := source_hybrid_primitive_of_jets hL hκ hρg Q
    P hP δ h2 hδ hsmall hzero h3 (hybridUpper base b) hf hf2 hfy
  refine ⟨Pr,hfPr,hgPr,r,hr,?_,hunique⟩
  intro x
  exact (source_hybrid_mean_identity hL hκ Q M ν G ρ R P base b htrace Pr hfPr r hr x).trans
    (source_outer_eq_jointOuter κ M ν G ρ R x)

end Bilevel.EndpointTransportResponse
