import Bilevel.ChiHierarchyNormalLocality
import Bilevel.ChiHierarchyInactive

/-! Construction-specific support for the already defined globally fixed
inactive hierarchy. The full normal space is public, and the old terminal
prefix suffices because the last atom is flattened at the fixed finest width. -/
noncomputable section
set_option maxHeartbeats 600000
open scoped BigOperators
namespace Bilevel.ChiCarrier
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem gradient_div_const_mem (W : Submodule ℝ F) {f : F → ℝ} (hf : ContDiff ℝ 3 f)
    (x : F) (c : ℝ) (hm : gradient f x∈W) : gradient (fun y => f y/c) x∈W := by
  simp only [div_eq_mul_inv]
  exact gradient_mul_mem W hf contDiff_const x hm (gradient_const_mem W _ _)

end Bilevel.ChiCarrier

namespace Bilevel.ChiOuter
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry ChiExtension ChiExtensionCalibration ZeroChainSchedule
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

variable {m : ℕ} (M : Node E) (D : Geometry F) (J : ℕ)
  (hm : J < m) (a : E) (x : Blocks m F) (W : Fin m → Submodule ℝ F)
  (hx : x∈knownSpace W) (r : ℕ → List ℕ → ℕ)
  (htree : TreeBlind D 0 J (by simpa using hm) W x r)
  (hhp : ∀ t,t < J → ∀ P,0<(D (t+1) P).parentWidth)
  (hw : ∀ t,t < J → ∀ P,(D (t+1) P).width≤(D (t+1) P).parentWidth)
  (hfuture : ∀ t,t < J → ∀ P,∀ i : Fin ((D t P).n+1),r t P ≤ i.val →
    r (t+1) (child P i.val)≤(D (t+1) (child P i.val)).n)
  (c θ : ℝ) (hc : 0<c) (hcs : c≤1/128) (hβ : 0<(D J []).width) (hθ : 1≤θ)
  (hell : ∀ P,0≤(D J P).ell) (hwidth : ∀ P,(D J P).width=(D J []).width)
  (hz : ∀ P,∀ k : Fin ((D J P).n+1),r J P ≤ k.val →
    |(D J P).coordinates (x ⟨J,hm⟩) k|≤width c (D J []).width θ (levels θ)/8)
  (s : ℕ) (coarseIndex radialIndex : Fin J → Fin s) (fineIndex : Fin s)
  (ρ R : ℕ → ℝ) (dn : ℝ) (hR : ∀ i : Fin J,0<R (i.val+1)) (q : Normals s)

include hm hx htree hhp hw hfuture hcs hell hwidth hz hR in
theorem hierarchyInactiveExtension_tangent_support :
    gradient (fun y => hierarchyInactiveExtension m M D J c θ hc hβ hθ s coarseIndex radialIndex fineIndex ρ R dn
      (pack (pack a y) q)) x∈knownSpace W := by
  have hpa : ContDiff ℝ 3 (fun y : Blocks m F => pack a y) :=
    (packLinear (X:=E) (Y:=Blocks m F)).contDiff.comp (contDiff_const.prodMk contDiff_id)
  have hpf : ContDiff ℝ 3 (fun y : Blocks m F => pack (pack a y) q) :=
    (packLinear (X:=Joint E (Blocks m F)) (Y:=Normals s)).contDiff.comp (hpa.prodMk contDiff_const)
  have hco (i : Fin J) : ContDiff ℝ 3 (fun y : Blocks m F =>
      coarseFamily m M D J i (pack a y)*SmallGapProfiles.normal (coarseWidths D J i) (q (coarseIndex i))) :=
    ((coarseFamily_contDiff m M D J i).comp hpa).mul contDiff_const
  have hfi : ContDiff ℝ 3 (fun y : Blocks m F => outerInactiveCoupling m M D J c θ
      (CompensatedMean.pack (Joint E (Blocks m F)) (pack a y) (q fineIndex) 0)) := by
    have hh := (outerInactiveNormal_contDiff m M D J c θ hc hβ hθ s fineIndex).comp hpf
    change ContDiff ℝ 3 (fun y : Blocks m F => outerInactiveNormal m M D J c θ hc hβ hθ s fineIndex
      (pack (pack a y) q)) at hh
    simpa only [outerInactiveNormal_inner_eq] using hh
  have hra := (radialSum_contDiff radialIndex (fun i => hierarchyBlock (E:=E) (F:=F) m (i.val+1))
    (fun i => hierarchyBlock_norm_le (E:=E) (F:=F) m (i.val+1)) (fun i => ρ (i.val+1)) (fun i => R (i.val+1)) dn).comp hpf
  have he : (fun y : Blocks m F => hierarchyInactiveExtension m M D J c θ hc hβ hθ s coarseIndex radialIndex fineIndex ρ R dn
    (pack (pack a y) q))=(fun y : Blocks m F =>
    ((∑ i : Fin J,coarseFamily m M D J i (pack a y)*
      SmallGapProfiles.normal (coarseWidths D J i) (q (coarseIndex i)))+
      outerInactiveCoupling m M D J c θ (CompensatedMean.pack (Joint E (Blocks m F)) (pack a y) (q fineIndex) 0))/dn+
    radialSum radialIndex (fun i => hierarchyBlock (E:=E) (F:=F) m (i.val+1))
      (fun i => hierarchyBlock_norm_le (E:=E) (F:=F) m (i.val+1))
      (fun i => ρ (i.val+1)) (fun i => R (i.val+1)) dn (pack (pack a y) q)) := by
    funext y
    simp only [hierarchyInactiveExtension,hierarchyInactiveHidden,sourceCoarseExtension,coarseSum,
      normalTerm_formula,outerInactiveNormal_inner_eq,add_div]
  rw [he]
  apply gradient_add_mem (knownSpace W) (((ContDiff.sum (fun i _ => hco i)).add hfi).div_const dn) hra x
  · apply gradient_div_const_mem (knownSpace W) ((ContDiff.sum (fun i _ => hco i)).add hfi) x dn
    apply gradient_add_mem (knownSpace W) (ContDiff.sum (fun i _ => hco i)) hfi x
    · apply gradient_sum_mem Finset.univ (knownSpace W) _ hco
      intro i _
      exact gradient_mul_mem (knownSpace W) ((coarseFamily_contDiff m M D J i).comp hpa) contDiff_const x
        (coarseFamily_inner_support M D J hm a x W r htree hhp hw hfuture i)
        (gradient_const_mem (knownSpace W) _ _)
    · exact outerInactiveCoupling_inner_support M D J hm a x W r htree c θ (q fineIndex) hc hcs hθ hell hwidth hz
  · exact hierarchyRadialSum_inner_support hm radialIndex ρ R dn hR a x q W hx

include hm hx htree hhp hw hfuture hcs hell hwidth hz hR in
theorem hierarchyInactiveExtension_normal_support :
    gradient (lowerSlice (hierarchyInactiveExtension m M D J c θ hc hβ hθ s coarseIndex radialIndex fineIndex ρ R dn) a)
      (pack x q)∈normalKnown W s := by
  have hf := hierarchyInactiveExtension_contDiff m M D J c θ hc hβ hθ s coarseIndex radialIndex fineIndex ρ R dn
    (fun i => (htree (i.val+1) [] (by omega) (by have := i.isLt;omega)).width_pos)
  apply (gradient_normalKnown_iff W x q ((lowerSlice_contDiff hf a).differentiable (by norm_num) _)).mpr
  exact hierarchyInactiveExtension_tangent_support M D J hm a x W hx r htree hhp hw hfuture
    c θ hc hcs hβ hθ hell hwidth hz s coarseIndex radialIndex fineIndex ρ R dn hR q

end Bilevel.ChiOuter
