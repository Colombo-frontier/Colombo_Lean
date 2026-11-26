import Bilevel.ChiOuterFineLocality
import Bilevel.ChiHierarchyRadialLocality

/-! Full construction-specific tangential support of the actual hierarchy
extension. Coarse carriers, deepest centered carrier, fine atoms, all outer
and inner selectors, every child release, and all public radial terms are
included. All normal arguments are arbitrary. -/
noncomputable section
set_option maxHeartbeats 400000
open scoped BigOperators
namespace Bilevel.ChiOuter
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry ChiExtension ChiExtensionCalibration
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem hierarchyExtension_tangent_support {m : ℕ} (M : Node E) (D : Geometry F) (J : ℕ)
    (hm : J < m) (a : E) (x : Blocks m F) (W : Fin m → Submodule ℝ F)
    (hx : x∈knownSpace W) (r : ℕ → List ℕ → ℕ)
    (htree : TreeBlind D 0 J (by simpa using hm) W x r)
    (hhp : ∀ t,t < J → ∀ P,0<(D (t+1) P).parentWidth)
    (hw : ∀ t,t < J → ∀ P,(D (t+1) P).width≤(D (t+1) P).parentWidth)
    (hfuture : ∀ t,t < J → ∀ P,∀ i : Fin ((D t P).n+1),r t P ≤ i.val →
      r (t+1) (child P i.val)≤(D (t+1) (child P i.val)).n)
    (c θ : ℝ) (hc : 0<c) (hcs : c≤1/128) (hβ : 0<(D J []).width) (hθ : 1≤θ)
    (hell : ∀ P,0≤(D J P).ell)
    (hnew : ∀ P,∀ k : Fin ((D J P).n+1),k.val=r J P → (D J P).frame (basis k)∈W ⟨J,hm⟩)
    (s : ℕ) (coarseIndex radialIndex : Fin J → Fin s) (fineIndex : Fin s)
    (ρ R : ℕ → ℝ) (dn : ℝ) (hR : ∀ i : Fin J,0<R (i.val+1)) (q : Normals s) :
    gradient (fun y => hierarchyExtension m M D J c θ hc hβ hθ s coarseIndex radialIndex fineIndex ρ R dn
      (pack (pack a y) q)) x∈knownSpace W := by
  have hpa : ContDiff ℝ 3 (fun y : Blocks m F => pack a y) :=
    (packLinear (X:=E) (Y:=Blocks m F)).contDiff.comp (contDiff_const.prodMk contDiff_id)
  have hpf : ContDiff ℝ 3 (fun y : Blocks m F => pack (pack a y) q) :=
    (packLinear (X:=Joint E (Blocks m F)) (Y:=Normals s)).contDiff.comp (hpa.prodMk contDiff_const)
  have hco (i : Fin J) : ContDiff ℝ 3 (fun y : Blocks m F =>
      coarseFamily m M D J i (pack a y)*SmallGapProfiles.normal (coarseWidth D (i.val+1)) (q (coarseIndex i))) :=
    ((coarseFamily_contDiff m M D J i).comp hpa).mul contDiff_const
  have hfi : ContDiff ℝ 3 (fun y : Blocks m F => outerCoupling m M D J c θ
      (CompensatedMean.pack (Joint E (Blocks m F)) (pack a y) (q fineIndex) 0)) := by
    have hh := (outerFineNormal_contDiff m M D J c θ hc hβ hθ s fineIndex).comp hpf
    change ContDiff ℝ 3 (fun y : Blocks m F => outerFineNormal m M D J c θ hc hβ hθ s fineIndex
      (pack (pack a y) q)) at hh
    simpa only [outerFineNormal_inner_eq] using hh
  have hra := (radialSum_contDiff radialIndex (fun i => hierarchyBlock (E:=E) (F:=F) m (i.val+1))
    (fun i => hierarchyBlock_norm_le (E:=E) (F:=F) m (i.val+1)) (fun i => ρ (i.val+1)) (fun i => R (i.val+1)) dn).comp hpf
  have he : (fun y : Blocks m F => hierarchyExtension m M D J c θ hc hβ hθ s coarseIndex radialIndex fineIndex ρ R dn
    (pack (pack a y) q))=(fun y : Blocks m F =>
    (1/dn)*((∑ i : Fin J,coarseFamily m M D J i (pack a y)*
      SmallGapProfiles.normal (coarseWidth D (i.val+1)) (q (coarseIndex i)))+
      outerCoupling m M D J c θ (CompensatedMean.pack (Joint E (Blocks m F)) (pack a y) (q fineIndex) 0))+
    radialSum radialIndex (fun i => hierarchyBlock (E:=E) (F:=F) m (i.val+1)) (fun i => hierarchyBlock_norm_le (E:=E) (F:=F) m (i.val+1))
      (fun i => ρ (i.val+1)) (fun i => R (i.val+1)) dn (pack (pack a y) q)) := by
    funext y
    simp only [hierarchyExtension,total,ChiExtension.hidden,coarseSum,normalTerm_formula]
    rfl
  rw [he]
  apply gradient_add_mem (knownSpace W)
    (contDiff_const.mul ((ContDiff.sum (fun i _ => hco i)).add hfi)) hra x
  · apply gradient_mul_mem (knownSpace W) contDiff_const ((ContDiff.sum (fun i _ => hco i)).add hfi) x
      (gradient_const_mem (knownSpace W) _ _)
    apply gradient_add_mem (knownSpace W) (ContDiff.sum (fun i _ => hco i)) hfi x
    · apply gradient_sum_mem Finset.univ (knownSpace W) _ hco
      intro i _
      exact gradient_mul_mem (knownSpace W) ((coarseFamily_contDiff m M D J i).comp hpa) contDiff_const x
        (coarseFamily_inner_support M D J hm a x W r htree hhp hw hfuture i)
        (gradient_const_mem (knownSpace W) _ _)
    · exact outerCoupling_inner_support M D J hm a x W r htree c θ (q fineIndex) hc hcs hθ hell hnew
  · exact hierarchyRadialSum_inner_support hm radialIndex ρ R dn hR a x q W hx

end Bilevel.ChiOuter
