import Bilevel.ChiFullDisclosureObjective
import Bilevel.ChiHierarchyInactive

/-! Global original-versus-complete-array identities for the upper base
and the two fixed normal extensions. No blind event is required here. -/
noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators
namespace Bilevel.ChiPrefixEvaluation
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry ChiOuter ChiExtension ChiExtensionCalibration
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem virtualOuterCarrier_full (m : ℕ) (M : Node E) (D : Geometry F) (d t : ℕ)
    (z : Joint E (Blocks m F)) :
    virtualOuterCarrier m M D (M.n+1) (fullCounts D) (nodeColumns M) (fullColumns D) d t z=
      outerCarrier m M D d t z := by
  simp only [virtualOuterCarrier,outerCarrier,outerSelected,virtualOuterSelector_full,virtualCarrier_full,jointCarrier,jointOuterSelector,Function.comp_apply]
  rfl

theorem virtualOuterLeaf_full (m : ℕ) (M : Node E) (D : Geometry F)
    (leaf : ∀ j I,Space (D j I).n → ℝ) (d : ℕ) (z : Joint E (Blocks m F)) :
    virtualOuterLeaf m M D (M.n+1) (fullCounts D) (nodeColumns M) (fullColumns D) leaf d z=
      outerSelected m M (fun i => selectFamily m D
        (fun j I x => leaf j I ((D j I).coordinates (block m j x))) d 0 [i.val]) z := by
  simp only [virtualOuterLeaf,outerSelected,virtualOuterSelector_full,virtualSelect_full,jointOuterSelector,Function.comp_apply]
  rfl

theorem virtualOuterFrontier_full (m : ℕ) (M : Node E) (D : Geometry F) (d : ℕ)
    (z : Joint E (Blocks m F)) :
    virtualOuterLeaf m M D (M.n+1) (fullCounts D) (nodeColumns M) (fullColumns D) (frontierLeaf D) d z=
      outerFineFrontier m M D d z :=
  virtualOuterLeaf_full m M D (frontierLeaf D) d z

theorem virtualOuterPiece_full (m : ℕ) (M : Node E) (D : Geometry F) (d : ℕ) (c v : ℝ) (p : ℕ)
    (z : Joint E (Blocks m F)) :
    virtualOuterLeaf m M D (M.n+1) (fullCounts D) (nodeColumns M) (fullColumns D) (pieceLeaf D c v p) d z=
      outerFinePiece m M D d c v p z :=
  virtualOuterLeaf_full m M D (pieceLeaf D c v p) d z

theorem virtualOuterSignal_full (m : ℕ) (M : Node E) (D : Geometry F) (d : ℕ) (τ : ℝ)
    (z : Joint E (Blocks m F)) :
    virtualOuterLeaf m M D (M.n+1) (fullCounts D) (nodeColumns M) (fullColumns D) (signalLeaf D τ) d z=
      outerFineSignal m M D d τ z :=
  virtualOuterLeaf_full m M D (signalLeaf D τ) d z

theorem virtualCoarse_full (m : ℕ) (M : Node E) (D : Geometry F) (J : ℕ) (i : Fin J)
    (z : Joint E (Blocks m F)) :
    virtualCoarse m M D (M.n+1) (fullCounts D) (nodeColumns M) (fullColumns D) J i z=
      coarseFamily m M D J i z := by
  simp only [virtualCoarse,coarseFamily,outerDeepestA,virtualOuterCarrier_full,virtualOuterFrontier_full]
  split_ifs <;> rfl

theorem virtualUpperBase_full (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F) (d : ℕ) (ρ R : ℝ)
    (z : Joint E (Blocks m F)) :
    virtualUpperBase m M ν D d ρ R (M.n+1) (fullCounts D) (nodeColumns M) (fullColumns D) z=
      upperBase m M ν D d ρ R z := by
  simp only [virtualUpperBase,upperBase,baseLower,virtualMacroValue_full,virtualOuterCarrier_full,
    virtualOuterReleaseCorrection,outerReleaseCorrection,virtualOuterResidual_full,fullCounts,fullColumns,
    virtualRelease_full,jointRelease,Function.comp_apply]

variable (m : ℕ) (M : Node E) (D : Geometry F) (J : ℕ) (c v : ℝ)
  (hc : 0<c) (hβ : 0<(D J []).width) (hv : 1≤v) (s : ℕ)
  (index radialIndex : Fin J → Fin s) (fineIndex : Fin s) (rad R : ℕ → ℝ) (dn : ℝ)

theorem virtualActive_full (z : Full (Joint E (Blocks m F)) s) :
    virtualActive m M D J (M.n+1) (fullCounts D) (nodeColumns M) (fullColumns D)
      c v s index radialIndex fineIndex rad R dn z=
    hierarchyExtension m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn z := by
  unfold hierarchyExtension total virtualActive
  congr 1
  unfold ChiExtension.hidden coarseSum
  congr 1
  apply congrArg₂ (fun a b : ℝ => a+b)
  · apply Finset.sum_congr rfl
    intro i _
    change _=normalTerm s (index i) _ _ (pack z.fst z.snd)
    rw [normalTerm_formula,virtualCoarse_full]
  · rw [fineTerm_sum]
    apply Finset.sum_congr rfl
    intro p _
    change _=normalTerm s fineIndex (outerFinePiece m M D J c v p)
      (ZeroChainSchedule.width c (D J []).width v p) (pack z.fst z.snd)
    rw [normalTerm_formula,virtualOuterPiece_full]

omit hc hβ hv index radialIndex rad R dn in
theorem virtualSignal_full (z : Full (Joint E (Blocks m F)) s) :
    virtualSignal m M D J (M.n+1) (fullCounts D) (nodeColumns M) (fullColumns D) c v s fineIndex z=
      outerSignalNormal m M D J c v s fineIndex z := by
  unfold virtualSignal outerSignalNormal
  dsimp only
  change _=normalTerm s fineIndex _ _ (pack z.fst z.snd)
  rw [normalTerm_formula,virtualOuterSignal_full]

theorem virtualInactive_full (z : Full (Joint E (Blocks m F)) s) :
    virtualInactive m M D J (M.n+1) (fullCounts D) (nodeColumns M) (fullColumns D)
      c v s index radialIndex fineIndex rad R dn z=
    hierarchyInactiveExtension m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn z := by
  unfold virtualInactive
  rw [virtualActive_full m M D J c v hc hβ hv,virtualSignal_full]
  have he := hierarchyInactiveExtension_difference m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn z
  linarith only [he]

end Bilevel.ChiPrefixEvaluation
