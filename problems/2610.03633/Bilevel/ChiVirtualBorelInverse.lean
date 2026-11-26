import Bilevel.ChiVirtualState
import Bilevel.ChiVirtualRegularity
import Bilevel.ParametricLowerSliceInverse

/-! A Borel inverse of the actual disclosed-column scalar evaluator. The
valid state set is exactly the prefix Gram certificate. Outside that set the
specified fallback is returned; inside it the inverse is the unique actual
partial-conjugate solution. -/
noncomputable section
open MeasureTheory
namespace Bilevel.ChiPrefixEvaluation
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry ChiExtension
set_option maxHeartbeats 1200000
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

def statePotential (active : Bool) (m : ℕ) (M : Node E) (D : Geometry F) (J : ℕ)
    (rM : ℕ → ℕ) (r : ℕ → ℕ → List ℕ → ℕ) (c v : ℝ) (s : ℕ)
    (index radialIndex : Fin J → Fin s) (fineIndex : Fin s) (rad R : ℕ → ℝ) (dn : ℝ)
    (p : VirtualState M D) : Full (Joint E (Blocks m F)) s → ℝ :=
  if active then virtualActive m M D J (rM p.1) (r p.1) p.2.1 p.2.2 c v s index radialIndex fineIndex rad R dn
    else virtualInactive m M D J (rM p.1) (r p.1) p.2.1 p.2.2 c v s index radialIndex fineIndex rad R dn

omit [CompleteSpace E] [CompleteSpace F] in
theorem statePotential_continuous (active : Bool) (m : ℕ) (M : Node E) (D : Geometry F) (J : ℕ)
    (rM : ℕ → ℕ) (r : ℕ → ℕ → List ℕ → ℕ) (c v : ℝ) (s : ℕ)
    (index radialIndex : Fin J → Fin s) (fineIndex : Fin s) (rad R : ℕ → ℝ) (dn : ℝ) :
    Continuous (Function.uncurry (statePotential active m M D J rM r c v s index radialIndex fineIndex rad R dn)) := by
  cases active with
  | false => exact virtualInactive_state_continuous m M D J rM r c v s index radialIndex fineIndex rad R dn
  | true => exact virtualActive_state_continuous m M D J rM r c v s index radialIndex fineIndex rad R dn

theorem statePotential_contDiff (active : Bool) (m : ℕ) (M : Node E) (D : Geometry F) (J : ℕ)
    (rM : ℕ → ℕ) (r : ℕ → ℕ → List ℕ → ℕ) (c v : ℝ) (hc : 0<c)
    (hβ : 0<(D J []).width) (hv : 1≤v) (s : ℕ)
    (index radialIndex : Fin J → Fin s) (fineIndex : Fin s) (rad R : ℕ → ℝ) (dn : ℝ)
    (hR : ∀ i : Fin J,0<R (i.val+1)) (hw : ∀ i : Fin J,0<(D (i.val+1) []).width)
    (p : VirtualState M D) (hp : ValidState M D rM r p) :
    ContDiff ℝ 3 (statePotential active m M D J rM r c v s index radialIndex fineIndex rad R dn p) := by
  cases active with
  | false =>
    exact virtualInactive_contDiff (A:=E) (B:=F) m M D J (rM p.1) (r p.1) p.2.1 p.2.2 M.frame
      (fun j I => (D j I).frame) hp.1 hp.2 c v hc hβ hv s index radialIndex fineIndex rad R dn hR hw
  | true =>
    exact virtualActive_contDiff (A:=E) (B:=F) m M D J (rM p.1) (r p.1) p.2.1 p.2.2 M.frame
      (fun j I => (D j I).frame) hp.1 hp.2 c v hc hβ hv s index radialIndex fineIndex rad R dn hR hw

variable (active : Bool) (m : ℕ) (M : Node E) (D : Geometry F) (J : ℕ)
  (rM : ℕ → ℕ) (r : ℕ → ℕ → List ℕ → ℕ) (c v : ℝ) (hc : 0<c)
  (hβ : 0<(D J []).width) (hv : 1≤v) (s : ℕ)
  (index radialIndex : Fin J → Fin s) (fineIndex : Fin s) (rad R : ℕ → ℝ) (dn : ℝ)
  (hR : ∀ i : Fin J,0<R (i.val+1)) (hw : ∀ i : Fin J,0<(D (i.val+1) []).width)
  (h2 : ∀ p : {p : VirtualState M D | ValidState M D rM r p},∀ z,
    ‖iteratedFDeriv ℝ 2 (statePotential active m M D J rM r c v s index radialIndex fineIndex rad R dn p.1) z‖≤1/12)

def stateInverse (outerPoint : VirtualState M D → E)
    (query fallback : VirtualState M D → Joint (Blocks m F) (Normals s)) :
    VirtualState M D → Joint (Blocks m F) (Normals s) :=
  ParametricScalarInverse.inverseSlice {p | ValidState M D rM r p}
    (statePotential active m M D J rM r c v s index radialIndex fineIndex rad R dn)
    outerPoint query fallback ⟨1/12,by norm_num⟩ (by change (1/12:ℝ)<1; norm_num)
    (fun p => statePotential_contDiff active m M D J rM r c v hc hβ hv s index radialIndex fineIndex rad R dn hR hw p.1 p.2) h2

theorem stateInverse_equation (outerPoint : VirtualState M D → E)
    (query fallback : VirtualState M D → Joint (Blocks m F) (Normals s))
    (p : VirtualState M D) (hp : ValidState M D rM r p) :
    let Z := stateInverse active m M D J rM r c v hc hβ hv s index radialIndex fineIndex rad R dn hR hw h2
      outerPoint query fallback p
    Z+gradient (lowerSlice (statePotential active m M D J rM r c v s index radialIndex fineIndex rad R dn p)
      (outerPoint p)) Z=query p :=
  ParametricScalarInverse.inverseSlice_equation _ _ outerPoint query fallback ⟨1/12,by norm_num⟩
    (by change (1/12:ℝ)<1; norm_num) _ h2 p hp

theorem stateInverse_eq_jointSolution (outerPoint : VirtualState M D → E)
    (query fallback : VirtualState M D → Joint (Blocks m F) (Normals s))
    (p : VirtualState M D) (hp : ValidState M D rM r p) :
    stateInverse active m M D J rM r c v hc hβ hv s index radialIndex fineIndex rad R dn hR hw h2
      outerPoint query fallback p=
    PartialLegendre.jointSolution
      (reassociated_gradient_lipschitz
        (statePotential_contDiff active m M D J rM r c v hc hβ hv s index radialIndex fineIndex rad R dn hR hw p hp)
        ⟨1/12,by norm_num⟩ (h2 ⟨p,hp⟩))
      (by change (1/12:ℝ)<1; norm_num) (outerPoint p) (query p) :=
  ParametricScalarInverse.inverseSlice_eq_jointSolution _ _ outerPoint query fallback ⟨1/12,by norm_num⟩
    (by change (1/12:ℝ)<1; norm_num) _ h2 p hp

variable [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
  [MeasurableSpace (Joint (Blocks m F) (Normals s))] [BorelSpace (Joint (Blocks m F) (Normals s))]

theorem stateInverse_measurable (outerPoint : VirtualState M D → E) (hm : Measurable outerPoint)
    (query fallback : VirtualState M D → Joint (Blocks m F) (Normals s))
    (hq : Measurable query) (hb : Measurable fallback) :
    Measurable (stateInverse active m M D J rM r c v hc hβ hv s index radialIndex fineIndex rad R dn hR hw h2
      outerPoint query fallback) :=
  ParametricScalarInverse.inverseSlice_measurable {p | ValidState M D rM r p}
    (validState_measurable M D rM r) _
    (statePotential_continuous active m M D J rM r c v s index radialIndex fineIndex rad R dn)
    outerPoint hm query fallback hq hb ⟨1/12,by norm_num⟩ (by change (1/12:ℝ)<1; norm_num) _ h2

end Bilevel.ChiPrefixEvaluation
