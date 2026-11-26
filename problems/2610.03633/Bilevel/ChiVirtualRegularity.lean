import Bilevel.ChiVirtualFormula

/-! The explicit disclosed-array evaluators inherit the certified regularity
of the completed actual source. No prefix-blindness assumption is used. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.ChiPrefixEvaluation
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry ChiExtension
variable {E F A B : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [CompleteSpace B]
variable (m : ℕ) (M : Node E) (D : Geometry F) (J rM : ℕ) (r : ℕ → List ℕ → ℕ)
  (macroColumns : Fin (M.n+1) → E) (columns : ∀ j I,Fin ((D j I).n+1) → F)
  (VM : Space M.n →ₗᵢ[ℝ] A) (V : ∀ j I,Space (D j I).n →ₗᵢ[ℝ] B)
  (hmGram : ∀ a b : Fin (M.n+1),a.val<rM → b.val<rM →
    ⟪macroColumns a,macroColumns b⟫=if a=b then 1 else 0)
  (hGram : ∀ j I,∀ a b : Fin ((D j I).n+1),a.val<r j I → b.val<r j I →
    ⟪columns j I a,columns j I b⟫=if a=b then 1 else 0)
  (c θ : ℝ) (hc : 0<c) (hβ : 0<(D J []).width) (hθ : 1≤θ)
  (s : ℕ) (index radialIndex : Fin J → Fin s) (fineIndex : Fin s) (rad R : ℕ → ℝ) (dn : ℝ)
  (hR : ∀ i : Fin J,0<R (i.val+1))

include VM V hmGram hGram hc hβ hθ hR

theorem virtualActive_contDiff (hw : ∀ i : Fin J,0<(D (i.val+1) []).width) :
    ContDiff ℝ 3 (virtualActive m M D J rM r macroColumns columns c θ s index radialIndex fineIndex rad R dn) := by
  have he := funext (activePotential_eq_virtualActive m M D J rM r macroColumns columns VM V hmGram hGram
    c θ hc hβ hθ s index radialIndex fineIndex rad R dn hR)
  rw [← he]
  exact activePotential_contDiff m M D J rM r macroColumns columns VM V hmGram hGram
    c θ hc hβ hθ s index radialIndex fineIndex rad R dn hw

theorem virtualInactive_contDiff (hw : ∀ i : Fin J,0<(D (i.val+1) []).width) :
    ContDiff ℝ 3 (virtualInactive m M D J rM r macroColumns columns c θ s index radialIndex fineIndex rad R dn) := by
  have he := funext (inactivePotential_eq_virtualInactive m M D J rM r macroColumns columns VM V hmGram hGram
    c θ hc hβ hθ s index radialIndex fineIndex rad R dn hR)
  rw [← he]
  exact inactivePotential_contDiff m M D J rM r macroColumns columns VM V hmGram hGram
    c θ hc hβ hθ s index radialIndex fineIndex rad R dn hw

theorem virtualActive_jet_eq (k : ℕ) (z : Full (Joint E (Blocks m F)) s) :
    iteratedFDeriv ℝ k (virtualActive m M D J rM r macroColumns columns c θ s index radialIndex fineIndex rad R dn) z=
    iteratedFDeriv ℝ k (activePotential m M D J rM r macroColumns columns VM V hmGram hGram
      c θ hc hβ hθ s index radialIndex fineIndex rad R dn) z := by
  rw [funext (activePotential_eq_virtualActive m M D J rM r macroColumns columns VM V hmGram hGram
    c θ hc hβ hθ s index radialIndex fineIndex rad R dn hR)]

theorem virtualInactive_jet_eq (k : ℕ) (z : Full (Joint E (Blocks m F)) s) :
    iteratedFDeriv ℝ k (virtualInactive m M D J rM r macroColumns columns c θ s index radialIndex fineIndex rad R dn) z=
    iteratedFDeriv ℝ k (inactivePotential m M D J rM r macroColumns columns VM V hmGram hGram
      c θ hc hβ hθ s index radialIndex fineIndex rad R dn) z := by
  rw [funext (inactivePotential_eq_virtualInactive m M D J rM r macroColumns columns VM V hmGram hGram
    c θ hc hβ hθ s index radialIndex fineIndex rad R dn hR)]

end Bilevel.ChiPrefixEvaluation
