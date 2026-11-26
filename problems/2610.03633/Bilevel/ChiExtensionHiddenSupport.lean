import Bilevel.ChiExtensionFineSupport
import Bilevel.ChiExtensionSum

/-! Normal embedding and finite summation preserve actual tangential
support. All normal coordinates are arbitrary. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiExtension
open PrimitiveGeometry ChiCarrier
variable {E T : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [CompleteSpace T]

theorem coarseSum_tangent_slice_support {n m : ℕ} (index : Fin n → Fin m)
    (f : Fin n → Joint E T → ℝ) (width : Fin n → ℝ)
    (hf : ∀ i,ContDiff ℝ 3 (f i)) (a : E) (q : Normals m) (W : Submodule ℝ T) (x : T)
    (he : ∀ i,gradient (fun y => f i (pack a y)) x∈W) :
    gradient (fun y => coarseSum index f width (pack (pack a y) q)) x∈W := by
  have hp : ContDiff ℝ 3 (fun y : T => pack a y) :=
    (packLinear (X:=E) (Y:=T)).contDiff.comp (contDiff_const.prodMk contDiff_id)
  have heq : (fun y : T => coarseSum index f width (pack (pack a y) q))=
      fun y : T => ∑ i : Fin n,f i (pack a y)*SmallGapProfiles.normal (width i) (q (index i)) := by
    funext y
    unfold coarseSum
    apply Finset.sum_congr rfl
    intro i _
    exact normalTerm_formula m (index i) (f i) (width i) (pack a y) q
  rw [heq]
  apply gradient_sum_mem Finset.univ W _ (fun i => ((hf i).comp hp).mul contDiff_const)
  intro i _
  exact gradient_mul_mem W ((hf i).comp hp) contDiff_const x (he i) (gradient_const_mem W _ x)

theorem hidden_tangent_slice_support {n m : ℕ} (index : Fin n → Fin m)
    (f : Fin n → Joint E T → ℝ) (width : Fin n → ℝ)
    (hf : ∀ i,ContDiff ℝ 3 (f i)) (hw : ∀ i,0<width i)
    (i : Fin m) (D : CompensatedMean.Data (E:=Joint E T)) (lambdaExt : ℝ)
    (a : E) (q : Normals m) (W : Submodule ℝ T) (x : T)
    (hfmem : ∀ j,gradient (fun y => f j (pack a y)) x∈W)
    (hemem : ∀ j,j≤D.J → gradient (fun y => D.e j (pack a y)) x∈W) :
    gradient (fun y => hidden index f width i D lambdaExt (pack (pack a y) q)) x∈W := by
  have hp : ContDiff ℝ 3 (fun y : T => pack (pack a y) q) :=
    (packLinear (X:=Joint E T) (Y:=Normals m)).contDiff.comp
      (((packLinear (X:=E) (Y:=T)).contDiff.comp (contDiff_const.prodMk contDiff_id)).prodMk contDiff_const)
  apply gradient_mul_mem W contDiff_const
    (((coarseSum_contDiff index f width hf hw).comp hp).add ((fineTerm_contDiff m i D).comp hp)) x
    (gradient_const_mem W lambdaExt x)
  exact gradient_add_mem W ((coarseSum_contDiff index f width hf hw).comp hp)
    ((fineTerm_contDiff m i D).comp hp) x
    (coarseSum_tangent_slice_support index f width hf a q W x hfmem)
    (fineTerm_tangent_slice_support D m i a q W x hemem)

end Bilevel.ChiExtension
