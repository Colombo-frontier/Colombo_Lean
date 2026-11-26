import Bilevel.ChiExtensionReadout
import Bilevel.ChiOuterUpperTrace
import Bilevel.ChiOuterCarrierFineData

/-! The concrete complete normal extension recovers the actual recursive
objective under the source's scalar upper readout. -/
noncomputable section
namespace Bilevel.ChiOuter
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry ChiExtension ChiExtensionCalibration
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

def hierarchyBlock (m j : ℕ) : Joint E (Blocks m F) →L[ℝ] F :=
  (block m j).comp (innerProjection (E:=E) (F:=F) m)

omit [CompleteSpace E] [CompleteSpace F] in
theorem hierarchyBlock_norm_le (m j : ℕ) : ‖hierarchyBlock (E:=E) (F:=F) m j‖≤1 := by
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  exact (mul_le_mul (block_norm_le (E:=F) m j) (innerProjection_norm_le (E:=E) (F:=F) m)
    (norm_nonneg (innerProjection (E:=E) (F:=F) m)) zero_le_one).trans_eq (one_mul _)

def coarseWidth (D : Geometry F) (j : ℕ) : ℝ := (D j []).width*(((D j []).n:ℝ)+1)^(1/3:ℝ)

omit [CompleteSpace F] in
theorem coarseWidth_pos (D : Geometry F) (j : ℕ) (hh : 0<(D j []).width) : 0<coarseWidth D j :=
  mul_pos hh (Real.rpow_pos_of_pos (by positivity) _)

def hierarchyExtension (m : ℕ) (M : Node E) (D : Geometry F) (J : ℕ)
    (c θ : ℝ) (hc : 0<c) (hβ : 0<(D J []).width) (hθ : 1≤θ)
    (s : ℕ) (coarseIndex radialIndex : Fin J → Fin s) (fineIndex : Fin s)
    (ρ R : ℕ → ℝ) (dn : ℝ) : Full (Joint E (Blocks m F)) s → ℝ :=
  total coarseIndex (coarseFamily m M D J) (fun i => coarseWidth D (i.val+1)) fineIndex
    (outerFineData m M D J c θ hc hβ hθ) (1/dn)
    radialIndex (fun i => hierarchyBlock m (i.val+1)) (fun i => hierarchyBlock_norm_le m (i.val+1))
    (fun i => ρ (i.val+1)) (fun i => R (i.val+1)) dn

theorem hierarchyExtension_contDiff (m : ℕ) (M : Node E) (D : Geometry F) (J : ℕ)
    (c θ : ℝ) (hc : 0<c) (hβ : 0<(D J []).width) (hθ : 1≤θ)
    (s : ℕ) (coarseIndex radialIndex : Fin J → Fin s) (fineIndex : Fin s)
    (ρ R : ℕ → ℝ) (dn : ℝ) (hw : ∀ i : Fin J,0<(D (i.val+1) []).width) :
    ContDiff ℝ 3 (hierarchyExtension m M D J c θ hc hβ hθ s coarseIndex radialIndex fineIndex ρ R dn) :=
  total_contDiff coarseIndex (coarseFamily m M D J) _ (coarseFamily_contDiff m M D J)
    (fun i => coarseWidth_pos D _ (hw i)) fineIndex _ _ radialIndex _ _ _ _ dn

theorem hierarchyExtension_zero_trace (m : ℕ) (M : Node E) (D : Geometry F) (J : ℕ)
    (c θ : ℝ) (hc : 0<c) (hβ : 0<(D J []).width) (hθ : 1≤θ)
    (s : ℕ) (coarseIndex radialIndex : Fin J → Fin s) (fineIndex : Fin s)
    (ρ R : ℕ → ℝ) (dn : ℝ) (hw : ∀ i : Fin J,0<(D (i.val+1) []).width)
    (p : Joint E (Blocks m F)) :
    hierarchyExtension m M D J c θ hc hβ hθ s coarseIndex radialIndex fineIndex ρ R dn (pack p 0)=0 :=
  total_zero_trace coarseIndex (coarseFamily m M D J) _ (fun i => coarseWidth_pos D _ (hw i))
    fineIndex _ _ radialIndex _ _ _ _ dn p

theorem hierarchyExtension_objective_trace (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F) (j : ℕ)
    (c θ : ℝ) (hc : 0<c) (hβ : 0<(D (j+1) []).width) (hθ : 1≤θ)
    (s : ℕ) (coarseIndex radialIndex : Fin (j+1) → Fin s) (fineIndex : Fin s)
    (ρ R : ℕ → ℝ) (dn : ℝ) (hdn : dn≠0)
    (hw : ∀ i : Fin (j+1),0<(D (i.val+1) []).width)
    (hR : ∀ i : Fin (j+1),0<R (i.val+1)) (p : Joint E (Blocks m F)) :
    upperBase m M ν D (j+1) (ρ 0) (R 0) p+
      dn*normalReadout s (gradient (fun q : Normals s =>
        hierarchyExtension m M D (j+1) c θ hc hβ hθ s coarseIndex radialIndex fineIndex ρ R dn (pack p q)) 0)=
      jointOuter m M ν D ρ R (j+1) 1 p := by
  have ht := total_normal_readout coarseIndex (coarseFamily m M D (j+1))
    (fun i => coarseWidth D (i.val+1)) (fun i => coarseWidth_pos D _ (hw i)) fineIndex
    (outerFineData m M D (j+1) c θ hc hβ hθ) radialIndex
    (fun i => hierarchyBlock m (i.val+1)) (fun i => hierarchyBlock_norm_le m (i.val+1))
    (fun i => ρ (i.val+1)) (fun i => R (i.val+1)) dn hdn hR p
  unfold hierarchyExtension
  rw [ht,upperBase_coarse_fine_trace]
  change _=upperBase m M ν D (j+1) (ρ 0) (R 0) p+
    (∑ i : Fin (j+1),coarseFamily m M D (j+1) i p)+outerFineFrontier m M D (j+1) p+
    ∑ i : Fin (j+1),RadialWrapper.bowl (ρ (i.val+1)) (R (i.val+1)) (block m (i.val+1) p.snd)
  change upperBase m M ν D (j+1) (ρ 0) (R 0) p+
    ((∑ i : Fin (j+1),coarseFamily m M D (j+1) i p)+outerFineFrontier m M D (j+1) p+
    ∑ i : Fin (j+1),RadialWrapper.bowl (ρ (i.val+1)) (R (i.val+1)) (block m (i.val+1) p.snd))=_
  ring

end Bilevel.ChiOuter
