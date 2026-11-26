import Bilevel.ChiVirtualSelection
import Bilevel.ChiHierarchyInactive

/-! The virtual active/inactive hierarchy is a restriction of an actual
completed source hierarchy in a larger finite Hilbert space. Consequently
its global Hessian budget is inherited isometrically; no blind-root choice
or unproved smallness of a truncated field is used. -/
noncomputable section
set_option maxHeartbeats 1200000
open scoped RealInnerProductSpace
namespace Bilevel.ChiPrefixEvaluation
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry ChiOuter ChiExtension
variable {E F A B : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [CompleteSpace B]

def fullInclusion (m s : ℕ) : Full (Joint E (Blocks m F)) s →ₗᵢ[ℝ]
    Full (Joint (Joint E A) (Blocks m (Joint F B))) s :=
  jointMap (jointMap (zeroInclusion (E:=E) (A:=A)) (blockInclusion (E:=F) (A:=B) m))
    (LinearIsometryEquiv.refl ℝ (Normals s)).toLinearIsometry

variable (m : ℕ) (M : Node E) (D : Geometry F) (J rM : ℕ) (r : ℕ → List ℕ → ℕ)
  (macroColumns : Fin (M.n+1) → E) (columns : ∀ j I,Fin ((D j I).n+1) → F)
  (VM : Space M.n →ₗᵢ[ℝ] A) (V : ∀ j I,Space (D j I).n →ₗᵢ[ℝ] B)
  (hmGram : ∀ a b : Fin (M.n+1),a.val<rM → b.val<rM →
    ⟪macroColumns a,macroColumns b⟫=if a=b then 1 else 0)
  (hGram : ∀ j I,∀ a b : Fin ((D j I).n+1),a.val<r j I → b.val<r j I →
    ⟪columns j I a,columns j I b⟫=if a=b then 1 else 0)
  (c θ : ℝ) (hc : 0<c) (hβ : 0<(D J []).width) (hθ : 1≤θ)
  (s : ℕ) (index radialIndex : Fin J → Fin s) (fineIndex : Fin s) (rad R : ℕ → ℝ) (dn : ℝ)

def activePotential : Full (Joint E (Blocks m F)) s → ℝ :=
  hierarchyExtension m (completedNode M rM macroColumns VM hmGram)
    (completedGeometry D r columns V hGram) J c θ hc hβ hθ s index radialIndex fineIndex rad R dn ∘
    fullInclusion m s

def inactivePotential : Full (Joint E (Blocks m F)) s → ℝ :=
  hierarchyInactiveExtension m (completedNode M rM macroColumns VM hmGram)
    (completedGeometry D r columns V hGram) J c θ hc hβ hθ s index radialIndex fineIndex rad R dn ∘
    fullInclusion m s

theorem activePotential_contDiff (hw : ∀ i : Fin J,0<(D (i.val+1) []).width) :
    ContDiff ℝ 3 (activePotential m M D J rM r macroColumns columns VM V hmGram hGram
      c θ hc hβ hθ s index radialIndex fineIndex rad R dn) :=
  (hierarchyExtension_contDiff m (completedNode M rM macroColumns VM hmGram)
    (completedGeometry D r columns V hGram) J c θ hc hβ hθ s index radialIndex fineIndex rad R dn hw).comp
    (by simpa only [LinearIsometry.coe_toContinuousLinearMap] using
      (fullInclusion (E:=E) (F:=F) (A:=A) (B:=B) m s).toContinuousLinearMap.contDiff (n:=3))

theorem inactivePotential_contDiff (hw : ∀ i : Fin J,0<(D (i.val+1) []).width) :
    ContDiff ℝ 3 (inactivePotential m M D J rM r macroColumns columns VM V hmGram hGram
      c θ hc hβ hθ s index radialIndex fineIndex rad R dn) :=
  (hierarchyInactiveExtension_contDiff m (completedNode M rM macroColumns VM hmGram)
    (completedGeometry D r columns V hGram) J c θ hc hβ hθ s index radialIndex fineIndex rad R dn hw).comp
    (by simpa only [LinearIsometry.coe_toContinuousLinearMap] using
      (fullInclusion (E:=E) (F:=F) (A:=A) (B:=B) m s).toContinuousLinearMap.contDiff (n:=3))

theorem activePotential_jet_bound (hw : ∀ i : Fin J,0<(D (i.val+1) []).width)
    (k : ℕ) (hk : k≤3) (C : ℝ)
    (hb : ∀ z,‖iteratedFDeriv ℝ k (hierarchyExtension m (completedNode M rM macroColumns VM hmGram)
      (completedGeometry D r columns V hGram) J c θ hc hβ hθ s index radialIndex fineIndex rad R dn) z‖≤C)
    (z : Full (Joint E (Blocks m F)) s) :
    ‖iteratedFDeriv ℝ k (activePotential m M D J rM r macroColumns columns VM V hmGram hGram
      c θ hc hβ hθ s index radialIndex fineIndex rad R dn) z‖≤C :=
  (isometric_jet_restriction (fullInclusion (E:=E) (F:=F) (A:=A) (B:=B) m s) _
    (hierarchyExtension_contDiff m (completedNode M rM macroColumns VM hmGram)
      (completedGeometry D r columns V hGram) J c θ hc hβ hθ s index radialIndex fineIndex rad R dn hw) z k hk).trans (hb _)

theorem inactivePotential_jet_bound (hw : ∀ i : Fin J,0<(D (i.val+1) []).width)
    (k : ℕ) (hk : k≤3) (C : ℝ)
    (hb : ∀ z,‖iteratedFDeriv ℝ k (hierarchyInactiveExtension m (completedNode M rM macroColumns VM hmGram)
      (completedGeometry D r columns V hGram) J c θ hc hβ hθ s index radialIndex fineIndex rad R dn) z‖≤C)
    (z : Full (Joint E (Blocks m F)) s) :
    ‖iteratedFDeriv ℝ k (inactivePotential m M D J rM r macroColumns columns VM V hmGram hGram
      c θ hc hβ hθ s index radialIndex fineIndex rad R dn) z‖≤C :=
  (isometric_jet_restriction (fullInclusion (E:=E) (F:=F) (A:=A) (B:=B) m s) _
    (hierarchyInactiveExtension_contDiff m (completedNode M rM macroColumns VM hmGram)
      (completedGeometry D r columns V hGram) J c θ hc hβ hθ s index radialIndex fineIndex rad R dn hw) z k hk).trans (hb _)

end Bilevel.ChiPrefixEvaluation
