import Bilevel.ChiVirtualBorelInverse

/-! Joint measurability in the disclosed state and both original query
components. Algorithm state and private randomness may choose those query
components independently of the disclosed-column arrays. -/
noncomputable section
open MeasureTheory
namespace Bilevel.ChiPrefixEvaluation
open ChiRecursive ChiCarrier PrimitiveGeometry ChiExtension
set_option maxHeartbeats 1200000
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

abbrev VirtualQuery (M : Node E) (D : Geometry F) (m s : ℕ) :=
  VirtualState M D × (E × Joint (Blocks m F) (Normals s))

variable (active : Bool) (m : ℕ) (M : Node E) (D : Geometry F) (J : ℕ)
  (rM : ℕ → ℕ) (r : ℕ → ℕ → List ℕ → ℕ) (c v : ℝ) (hc : 0<c)
  (hβ : 0<(D J []).width) (hv : 1≤v) (s : ℕ)
  (index radialIndex : Fin J → Fin s) (fineIndex : Fin s) (rad R : ℕ → ℝ) (dn : ℝ)
  (hR : ∀ i : Fin J,0<R (i.val+1)) (hw : ∀ i : Fin J,0<(D (i.val+1) []).width)
  (h2 : ∀ p : {p : VirtualState M D | ValidState M D rM r p},∀ z,
    ‖iteratedFDeriv ℝ 2 (statePotential active m M D J rM r c v s index radialIndex fineIndex rad R dn p.1) z‖≤1/12)

@[irreducible] def queryInverse : VirtualQuery M D m s → Joint (Blocks m F) (Normals s) :=
  ParametricScalarInverse.inverseSlice {p : VirtualQuery M D m s | ValidState M D rM r p.1}
    (fun p => statePotential active m M D J rM r c v s index radialIndex fineIndex rad R dn p.1)
    (fun p => p.2.1) (fun p => p.2.2) (fun _ => 0) ⟨1/12,by norm_num⟩
    (by change (1/12:ℝ)<1; norm_num)
    (fun p => statePotential_contDiff active m M D J rM r c v hc hβ hv s index radialIndex fineIndex rad R dn hR hw p.1.1 p.2)
    (fun p => h2 ⟨p.1.1,p.2⟩)

theorem queryInverse_eq_jointSolution (p : VirtualQuery M D m s) (hp : ValidState M D rM r p.1) :
    queryInverse active m M D J rM r c v hc hβ hv s index radialIndex fineIndex rad R dn hR hw h2 p=
    PartialLegendre.jointSolution
      (reassociated_gradient_lipschitz
        (statePotential_contDiff active m M D J rM r c v hc hβ hv s index radialIndex fineIndex rad R dn hR hw p.1 hp)
        ⟨1/12,by norm_num⟩ (h2 ⟨p.1,hp⟩))
      (by change (1/12:ℝ)<1; norm_num) p.2.1 p.2.2 := by
  unfold queryInverse
  exact ParametricScalarInverse.inverseSlice_eq_jointSolution _ _ _ _ _ ⟨1/12,by norm_num⟩
    (by change (1/12:ℝ)<1; norm_num) _ _ p hp

variable [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
  [MeasurableSpace (Joint (Blocks m F) (Normals s))] [BorelSpace (Joint (Blocks m F) (Normals s))]

theorem queryInverse_measurable :
    Measurable (queryInverse active m M D J rM r c v hc hβ hv s index radialIndex fineIndex rad R dn hR hw h2) := by
  letI : SecondCountableTopology (Joint (Blocks m F) (Normals s)) := inferInstance
  letI : BorelSpace (VirtualState M D) := inferInstance
  letI : SecondCountableTopology (VirtualState M D) := inferInstance
  letI : BorelSpace (E × Joint (Blocks m F) (Normals s)) := inferInstance
  letI : SecondCountableTopology (E × Joint (Blocks m F) (Normals s)) := inferInstance
  letI : OpensMeasurableSpace (VirtualQuery M D m s) := inferInstance
  unfold queryInverse
  have hS : MeasurableSet {p : VirtualQuery M D m s | ValidState M D rM r p.1} :=
    (validState_measurable M D rM r).preimage measurable_fst
  let pull : VirtualQuery M D m s × Full (Joint E (Blocks m F)) s →
      VirtualState M D × Full (Joint E (Blocks m F)) s := fun p => (p.1.1,p.2)
  have hpull : Continuous pull := continuous_fst.fst.prodMk continuous_snd
  have hcP := (statePotential_continuous active m M D J rM r c v s index radialIndex fineIndex rad R dn).comp hpull
  exact ParametricScalarInverse.inverseSlice_measurable (P:=VirtualQuery M D m s) (X:=E)
    (U:=Blocks m F) (V:=Normals s) _ hS
    (fun p => statePotential active m M D J rM r c v s index radialIndex fineIndex rad R dn p.1) hcP
    (fun p => p.2.1) measurable_snd.fst (fun p => p.2.2) (fun _ => 0)
    measurable_snd.snd measurable_const ⟨1/12,by norm_num⟩ (by change (1/12:ℝ)<1; norm_num) _ _

end Bilevel.ChiPrefixEvaluation
