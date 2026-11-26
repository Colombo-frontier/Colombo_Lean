import Bilevel.ChiNormalSignalSmall
import Bilevel.ChiHierarchyInactiveInverse
import Bilevel.ChiFineInactiveAtoms

/-! The actual hierarchy signal is compact in its single fine normal.
Small active/inactive Hessians therefore make its FULL lower gradient small
relative to the normal width, without a bound on either hidden gradient. -/
noncomputable section
set_option maxHeartbeats 800000
namespace Bilevel.ChiOuter
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry ChiExtension ZeroChainSchedule
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem hierarchy_lower_difference_normalTerm (m : ℕ) (M : Node E) (D : Geometry F) (J : ℕ)
    (c v : ℝ) (hc : 0<c) (hβ : 0<(D J []).width) (hv : 1≤v)
    (s : ℕ) (index radialIndex : Fin J → Fin s) (fineIndex : Fin s) (rad R : ℕ → ℝ)
    (dn : ℝ) (a : E) (z : Full (Blocks m F) s) :
    lowerSlice (hierarchyExtension m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn) a z-
      lowerSlice (hierarchyInactiveExtension m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn) a z=
    normalTerm s fineIndex
      (fun x => outerFineSignal m M D J (width c (D J []).width v (levels v)/8) (pack a x))
      (width c (D J []).width v (levels v)) z/dn := by
  unfold lowerSlice
  rw [hierarchyInactiveExtension_difference]
  change normalTerm s fineIndex (outerFineSignal m M D J (width c (D J []).width v (levels v)/8))
    (width c (D J []).width v (levels v)) (pack (pack a z.fst) z.snd)/dn=_
  change _=normalTerm s fineIndex
    (fun x => outerFineSignal m M D J (width c (D J []).width v (levels v)/8) (pack a x))
    (width c (D J []).width v (levels v)) (pack z.fst z.snd)/dn
  rw [normalTerm_formula,normalTerm_formula]

theorem hierarchy_lower_signal_bound (m : ℕ) (M : Node E) (D : Geometry F) (J : ℕ)
    (c v : ℝ) (hc : 0<c) (hβ : 0<(D J []).width) (hv : 1≤v)
    (s : ℕ) (index radialIndex : Fin J → Fin s) (fineIndex : Fin s) (rad R : ℕ → ℝ)
    (dn : ℝ) (hw : ∀ i : Fin J,0<(D (i.val+1) []).width)
    (δa δi : NNReal)
    (ha : ∀ z,‖iteratedFDeriv ℝ 2
      (hierarchyExtension m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn) z‖≤(δa:ℝ))
    (hi : ∀ z,‖iteratedFDeriv ℝ 2
      (hierarchyInactiveExtension m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn) z‖≤(δi:ℝ))
    (a : E) (z : Full (Blocks m F) s) :
    ‖gradient (lowerSlice (hierarchyExtension m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn) a) z-
      gradient (lowerSlice (hierarchyInactiveExtension m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn) a) z‖≤
      3*((δa:ℝ)+(δi:ℝ))*width c (D J []).width v (levels v) := by
  let Fa := hierarchyExtension m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn
  let Fi := hierarchyInactiveExtension m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn
  have hFa : ContDiff ℝ 3 Fa := hierarchyExtension_contDiff m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn hw
  have hFi : ContDiff ℝ 3 Fi := hierarchyInactiveExtension_contDiff m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn hw
  have hga := lowerSlice_gradient_lipschitz hFa δa ha a
  have hgi := lowerSlice_gradient_lipschitz hFi δi hi a
  let W := width c (D J []).width v (levels v)
  let f := fun x : Blocks m F => outerFineSignal m M D J (W/8) (pack a x)
  have he : (fun y => lowerSlice Fa a y-lowerSlice Fi a y)=(fun y => normalTerm s fineIndex f W y/dn) :=
    funext (hierarchy_lower_difference_normalTerm m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn a)
  have hg : gradient (fun y => normalTerm s fineIndex f W y/dn)=
      fun y => gradient (lowerSlice Fa a) y-gradient (lowerSlice Fi a) y := by
    rw [← he]
    funext y
    exact ChiFine.gradient_sub_C3 (lowerSlice_contDiff hFa a) (lowerSlice_contDiff hFi a) y
  have hLip : LipschitzWith (δa+δi) (gradient (fun y => normalTerm s fineIndex f W y/dn)) := by
    rw [hg]
    exact hga.sub hgi
  have hh := normalTerm_compact_gradient_bound s fineIndex f W dn
    (width_pos c _ v hc hβ hv _) (δa+δi) hLip z
  rw [hg] at hh
  exact hh

end Bilevel.ChiOuter
