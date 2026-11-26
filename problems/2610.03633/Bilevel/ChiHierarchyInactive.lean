import Bilevel.ChiOuterExtensionTrace
import Bilevel.ChiOuterCarrierInactiveBounds
import Bilevel.ChiSourceCoarseExtension

/-! The fixed inactive potential on the complete hierarchy. Only the last
deepest normal atom changes; the macro, ancestor and public radial terms
are identical. Its definition has no transcript or revealed-prefix input. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace Bilevel.ChiOuter
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry ChiExtension ChiExtensionCalibration
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

def hierarchyInactiveHidden (m : ℕ) (M : Node E) (D : Geometry F) (J : ℕ)
    (c v : ℝ) (hc : 0 < c) (hβ : 0 < (D J []).width) (hv : 1 ≤ v)
    (s : ℕ) (index : Fin J → Fin s) (fineIndex : Fin s) (dn : ℝ)
    (z : Full (Joint E (Blocks m F)) s) : ℝ :=
  sourceCoarseExtension m s M D J index dn z+outerInactiveNormal m M D J c v hc hβ hv s fineIndex z/dn

def hierarchyInactiveExtension (m : ℕ) (M : Node E) (D : Geometry F) (J : ℕ)
    (c v : ℝ) (hc : 0 < c) (hβ : 0 < (D J []).width) (hv : 1 ≤ v)
    (s : ℕ) (index radialIndex : Fin J → Fin s) (fineIndex : Fin s) (rad R : ℕ → ℝ) (dn : ℝ)
    (z : Full (Joint E (Blocks m F)) s) : ℝ :=
  hierarchyInactiveHidden m M D J c v hc hβ hv s index fineIndex dn z+
    radialSum radialIndex (fun i => hierarchyBlock (E:=E) (F:=F) m (i.val+1))
      (fun i => hierarchyBlock_norm_le (E:=E) (F:=F) m (i.val+1))
      (fun i => rad (i.val+1)) (fun i => R (i.val+1)) dn z

variable (m : ℕ) (M : Node E) (D : Geometry F) (J : ℕ)
  (c v : ℝ) (hc : 0 < c) (hβ : 0 < (D J []).width) (hv : 1 ≤ v)
  (s : ℕ) (index radialIndex : Fin J → Fin s) (fineIndex : Fin s) (rad R : ℕ → ℝ) (dn : ℝ)

theorem hierarchyInactiveHidden_contDiff (hw : ∀ i : Fin J,0 < (D (i.val+1) []).width) :
    ContDiff ℝ 3 (hierarchyInactiveHidden m M D J c v hc hβ hv s index fineIndex dn) :=
  ((coarseSum_contDiff index (coarseFamily m M D J) (coarseWidths D J)
    (coarseFamily_contDiff m M D J) (fun i => coarseWidth_pos D _ (hw i))).div_const dn).add
      ((outerInactiveNormal_contDiff m M D J c v hc hβ hv s fineIndex).div_const dn)

theorem hierarchyInactiveExtension_contDiff (hw : ∀ i : Fin J,0 < (D (i.val+1) []).width) :
    ContDiff ℝ 3 (hierarchyInactiveExtension m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn) :=
  (hierarchyInactiveHidden_contDiff m M D J c v hc hβ hv s index fineIndex dn hw).add
    (radialSum_contDiff radialIndex _ _ _ _ dn)

theorem hierarchyInactiveHidden_difference (z : Full (Joint E (Blocks m F)) s) :
    hidden index (coarseFamily m M D J) (coarseWidths D J) fineIndex
      (outerFineData m M D J c v hc hβ hv) (1/dn) z-
      hierarchyInactiveHidden m M D J c v hc hβ hv s index fineIndex dn z=
    outerSignalNormal m M D J c v s fineIndex z/dn := by
  dsimp only [ChiExtension.hidden,hierarchyInactiveHidden,sourceCoarseExtension,outerInactiveNormal,outerFineNormal]
  ring

theorem hierarchyInactiveExtension_difference (z : Full (Joint E (Blocks m F)) s) :
    hierarchyExtension m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn z-
      hierarchyInactiveExtension m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn z=
    outerSignalNormal m M D J c v s fineIndex z/dn := by
  unfold hierarchyExtension total hierarchyInactiveExtension
  rw [add_sub_add_right_eq_sub]
  exact hierarchyInactiveHidden_difference m M D J c v hc hβ hv s index fineIndex dn z

theorem hierarchyInactiveExtension_zero_trace (hw : ∀ i : Fin J,0 < (D (i.val+1) []).width)
    (p : Joint E (Blocks m F)) :
    hierarchyInactiveExtension m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn (pack p 0)=0 := by
  have hh := hierarchyInactiveExtension_difference m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn (pack p 0)
  rw [hierarchyExtension_zero_trace m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn hw,
    outerSignalNormal_zero_trace m M D J c v hc hβ hv,zero_div] at hh
  linarith

theorem hierarchyInactiveHidden_jet_bound (hw : ∀ i : Fin J,0 < (D (i.val+1) []).width)
    (z : Full (Joint E (Blocks m F)) s) (k : ℕ) (hk : k ≤ 3) (Bc Bf : ℝ)
    (hcoarse : ‖iteratedFDeriv ℝ k (sourceCoarseExtension m s M D J index dn) z‖ ≤ Bc)
    (hfine : ‖iteratedFDeriv ℝ k (fun q => outerInactiveNormal m M D J c v hc hβ hv s fineIndex q/dn) z‖ ≤ Bf) :
    ‖iteratedFDeriv ℝ k (hierarchyInactiveHidden m M D J c v hc hβ hv s index fineIndex dn) z‖ ≤ Bc+Bf := by
  have hk' : (k:WithTop ℕ∞) ≤ 3 := by exact_mod_cast hk
  have hcc := (coarseSum_contDiff index (coarseFamily m M D J) (coarseWidths D J)
    (coarseFamily_contDiff m M D J) (fun i => coarseWidth_pos D _ (hw i))).div_const dn
  have hfc := (outerInactiveNormal_contDiff m M D J c v hc hβ hv s fineIndex).div_const dn
  change ContDiff ℝ 3 (sourceCoarseExtension m s M D J index dn) at hcc
  unfold hierarchyInactiveHidden
  rw [iteratedFDeriv_add_apply' ((hcc.of_le hk').contDiffAt) ((hfc.of_le hk').contDiffAt)]
  exact (norm_add_le _ _).trans (add_le_add hcoarse hfine)

theorem hierarchyInactiveExtension_jet_bound (hw : ∀ i : Fin J,0 < (D (i.val+1) []).width)
    (z : Full (Joint E (Blocks m F)) s) (k : ℕ) (hk : k ≤ 3) (Ba Bs : ℝ)
    (ha : ‖iteratedFDeriv ℝ k (hierarchyExtension m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn) z‖ ≤ Ba)
    (hs : ‖iteratedFDeriv ℝ k (fun q => outerSignalNormal m M D J c v s fineIndex q/dn) z‖ ≤ Bs) :
    ‖iteratedFDeriv ℝ k (hierarchyInactiveExtension m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn) z‖ ≤ Ba+Bs := by
  have he : hierarchyInactiveExtension m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn=
      fun q => hierarchyExtension m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn q-
        outerSignalNormal m M D J c v s fineIndex q/dn := by
    funext q
    linarith [hierarchyInactiveExtension_difference m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn q]
  have hk' : (k:WithTop ℕ∞) ≤ 3 := by exact_mod_cast hk
  rw [he]
  simp only [sub_eq_add_neg]
  rw [iteratedFDeriv_add_apply'
    (((hierarchyExtension_contDiff m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn hw).of_le hk').contDiffAt)
    (((((outerSignalNormal_contDiff m M D J c v hc hβ hv s fineIndex).div_const dn).neg).of_le hk').contDiffAt)]
  have hneg : iteratedFDeriv ℝ k (fun q => -(outerSignalNormal m M D J c v s fineIndex q/dn)) z=
      -iteratedFDeriv ℝ k (fun q => outerSignalNormal m M D J c v s fineIndex q/dn) z :=
    iteratedFDeriv_neg_apply
  rw [hneg]
  exact (norm_add_le _ _).trans (add_le_add ha (by simpa only [norm_neg] using hs))

end Bilevel.ChiOuter
