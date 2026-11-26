import Bilevel.ChiHierarchyInactive
import Bilevel.ChiNormalizedExtensionJets

/-! The actual global active/inactive difference keeps the finest normal
width in its informative first-derivative bound. Common radial fields cancel. -/
noncomputable section
namespace Bilevel.ChiOuter
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry ChiExtension ChiExtensionCalibration
open ZeroChainSchedule
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem hierarchy_difference_first_bound (m : ℕ) (M : Node E) (D : Geometry F) (J : ℕ)
    (c v : ℝ) (hc : 0 < c) (hβ : 0 < (D J []).width) (hv : 1 ≤ v)
    (s : ℕ) (index radialIndex : Fin J → Fin s) (fineIndex : Fin s) (rad R : ℕ → ℝ)
    (dn : ℝ) (hdn : 0 < dn) (B : ℝ)
    (hsignal : ∀ z,‖iteratedFDeriv ℝ 1 (outerSignalNormal m M D J c v s fineIndex) z‖ ≤ B)
    (z : Full (Joint E (Blocks m F)) s) :
    ‖iteratedFDeriv ℝ 1 (fun q => hierarchyExtension m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn q-
      hierarchyInactiveExtension m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn q) z‖ ≤ B/dn := by
  have he : (fun q => hierarchyExtension m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn q-
      hierarchyInactiveExtension m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn q)=
      fun q => outerSignalNormal m M D J c v s fineIndex q/dn :=
    funext (hierarchyInactiveExtension_difference m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn)
  rw [he,normalized_jet_norm (outerSignalNormal_contDiff m M D J c v hc hβ hv s fineIndex) hdn 1 (by norm_num)]
  exact div_le_div_of_nonneg_right (hsignal z) hdn.le

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] in
theorem source_hierarchy_signal_envelope : ∃ B : ℝ,1 ≤ B ∧
    ∀ (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (n : ℕ) (initial : Scale),0 < initial.curvature → 0 < initial.width →
      ∀ (r η b : ℕ → ℝ) (A K ζ cn CR Km : ℝ),(∀ j,1 ≤ r j) → (∀ j,0 < η j) → (∀ j,η j ≤ 1) →
      (∀ j,0 < b j) → (∀ j,b j ≤ 1) → 1 ≤ K → 0 < ζ → ζ ≤ 1 → 1 ≤ CR → 1 ≤ Km →
      ∀ (U : Space n →ₗᵢ[ℝ] E)
        (V : ∀ j,List ℕ → Space (sourceChainIndex cn (r j) (η j)) →ₗᵢ[ℝ] F),
      let M := sourceMacroNode n initial Km U
      let D := sourceGeometry initial r η b A K ζ cn CR V
      ∀ (J m s : ℕ) (c v : ℝ),∀ hc : 0 < c,c ≤ 1/128 → ∀ hv : 1 ≤ v,
      ∀ hβ : 0 < (D J []).width,
      ∀ (index radialIndex : Fin J → Fin s) (fineIndex : Fin s) (rad R : ℕ → ℝ)
        (dn : ℝ),0 < dn → ∀ z : Full (Joint E (Blocks m F)) s,
      ‖iteratedFDeriv ℝ 1 (fun q => hierarchyExtension m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn q-
        hierarchyInactiveExtension m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn q) z‖ ≤
      2*SmallGapLiftSupport.C*B^(J+2)*(D J []).ell*(D J []).width*
        width c (D J []).width v (levels v)/dn := by
  obtain ⟨B,hB,hledger⟩ := source_outer_signal_normal_jets
  refine ⟨B,hB,?_⟩
  intro E F _ _ _ _ _ _ n initial hl hw r η b A K ζ cn CR Km hr hη hη1 hb hb1 hK hζ hζ1 hCR hKm U V
  dsimp only
  let M := sourceMacroNode n initial Km U
  let D := sourceGeometry initial r η b A K ζ cn CR V
  intro J m s c v hc hcs hv hβ index radialIndex fineIndex rad R dn hdn z
  exact hierarchy_difference_first_bound m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn hdn _
    (fun q => (hledger E F n initial hl hw r η b A K ζ cn CR Km hr hη hη1 hb hb1 hK hζ hζ1 hCR hKm
      U V J m c v hc hcs hv s fineIndex q).1) z

end Bilevel.ChiOuter
