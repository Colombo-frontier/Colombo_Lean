import Bilevel.ChiOuterExtensionTrace
import Bilevel.ChiExtensionResponse

/-! The actual complete source response is zero at the origin, including
all normal coordinates. Thus its lower initialization certificate is exact. -/
noncomputable section
namespace Bilevel.ChiOuter
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry ChiExtension ChiExtensionCalibration
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem coarseFamily_origin (m : ℕ) (M : Node E) (D : Geometry F) (J : ℕ) (i : Fin J) :
    coarseFamily m M D J i 0=0 := by
  unfold coarseFamily
  split_ifs <;> simp [outerDeepestA,outerCarrier,outerFineFrontier,outerSelected,
    jointCarrier_zero,selectedFineFrontier_zero]

theorem hierarchy_normalTrace_origin (m : ℕ) (M : Node E) (D : Geometry F) (J : ℕ)
    (c v : ℝ) (hc : 0<c) (hβ : 0<(D J []).width) (hv : 1≤v)
    (s : ℕ) (index radialIndex : Fin J → Fin s) (fineIndex : Fin s) (rad R : ℕ → ℝ) (dn : ℝ)
    (hw : ∀ i : Fin J,0<(D (i.val+1) []).width) (hR : ∀ i : Fin J,0<R (i.val+1)) :
    normalTrace (hierarchyExtension m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn) 0 0=0 := by
  change gradient (fun q : Normals s =>
    total index (coarseFamily m M D J) (fun i => coarseWidth D (i.val+1)) fineIndex
      (outerFineData m M D J c v hc hβ hv) (1/dn)
      radialIndex (fun i => hierarchyBlock (E:=E) (F:=F) m (i.val+1))
      (fun i => hierarchyBlock_norm_le m (i.val+1))
      (fun i => rad (i.val+1)) (fun i => R (i.val+1)) dn (pack 0 q)) 0=0
  rw [(total_normal_gradient index (coarseFamily m M D J) (fun i => coarseWidth D (i.val+1)) (fun i => coarseWidth_pos D _ (hw i))
    fineIndex (outerFineData m M D J c v hc hβ hv) (1/dn) radialIndex
    (fun i => hierarchyBlock (E:=E) (F:=F) m (i.val+1)) (fun i => hierarchyBlock_norm_le m (i.val+1))
    (fun i => rad (i.val+1)) (fun i => R (i.val+1)) dn hR 0).gradient]
  simp [coarseFamily_origin,(outerFineData_zero m M D J c v hc hβ hv).2]
  simp [EuclideanSpace.single]

theorem hierarchy_response_origin (m : ℕ) (M : Node E) (D : Geometry F) (J : ℕ)
    (c v : ℝ) (hc : 0<c) (hβ : 0<(D J []).width) (hv : 1≤v)
    (s : ℕ) (index radialIndex : Fin J → Fin s) (fineIndex : Fin s) (rad R : ℕ → ℝ) (dn : ℝ)
    (hw : ∀ i : Fin J,0<(D (i.val+1) []).width) (hR : ∀ i : Fin J,0<R (i.val+1))
    (r : Joint E (Blocks m F) → Joint (Blocks m F) (Normals s)) (K : ℝ)
    (hr : ∀ x,r x=pack (K • x.snd)
      (normalTrace (hierarchyExtension m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn) x.fst (K • x.snd))) :
    r 0=0 := by
  rw [hr]
  change pack (K • (0:Blocks m F))
    (normalTrace (hierarchyExtension m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn) 0 (K • (0:Blocks m F)))=0
  rw [smul_zero,hierarchy_normalTrace_origin m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn hw hR]
  rfl

end Bilevel.ChiOuter
