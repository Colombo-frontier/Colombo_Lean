import Bilevel.ChiExtensionFineTrace
import Bilevel.ChiCarrierSupportAlgebra

/-! Actual normal embedding preserves the tangential support of every
finite fine atom. Normal coordinates are arbitrary and every summand is
differentiated before using the known-space algebra. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiExtension
open PrimitiveGeometry ChiCarrier
variable {E T : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [CompleteSpace T]

omit [CompleteSpace E] in
theorem fineTerm_tangent_slice_support (D : CompensatedMean.Data (E:=Joint E T))
    (m : ℕ) (i : Fin m) (a : E) (q : Normals m) (W : Submodule ℝ T) (x : T)
    (he : ∀ j,j≤D.J → gradient (fun y => D.e j (pack a y)) x∈W) :
    gradient (fun y => fineTerm m i D (pack (pack a y) q)) x∈W := by
  have hp : ContDiff ℝ 3 (fun y : T => pack a y) :=
    (packLinear (X:=E) (Y:=T)).contDiff.comp (contDiff_const.prodMk contDiff_id)
  have heq : (fun y : T => fineTerm m i D (pack (pack a y) q))=
      fun y : T => ∑ j ∈ Finset.range (D.J+1),D.e j (pack a y)*SmallGapProfiles.normal (D.w j) (q i) := by
    funext y
    rw [fineTerm_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact normalTerm_formula m i (D.e j) (D.w j) (pack a y) q
  rw [heq]
  apply gradient_sum_mem _ W _ (fun j => ((D.e_smooth j).comp hp).mul contDiff_const)
  intro j hj
  exact gradient_mul_mem W ((D.e_smooth j).comp hp) contDiff_const x
    (he j (by have := Finset.mem_range.mp hj;omega)) (gradient_const_mem W _ x)

end Bilevel.ChiExtension

