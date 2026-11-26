import Bilevel.ChiOuterCarrierFineSupport
import Bilevel.ChiOuterCarrierDeepest
import Bilevel.ChiCarrierFineData
import Bilevel.ChiExtensionFineTrace

/-! Complete outer-selected fine decomposition packaged for actual normal
extension, with zero trace, exact normal derivative and proved overlap. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiOuter
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry ZeroChainSchedule
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

def outerFineData (m : ℕ) (M : Node E) (D : Geometry F) (d : ℕ) (c θ : ℝ)
    (hc : 0<c) (hβ : 0<(D d []).width) (hθ : 1≤θ) : CompensatedMean.Data (E:=Joint E (Blocks m F)) where
  μ := 1
  L := 1
  J := levels θ
  r := outerFineFrontier m M D d
  A := outerDeepestA m M D d
  e := outerFinePiece m M D d c θ
  w := width c (D d []).width θ
  r_smooth := outerFineFrontier_contDiff m M D d
  A_smooth := outerDeepestA_contDiff m M D d
  e_smooth := outerFinePiece_contDiff m M D d c θ
  w_pos := fun p _ => width_pos c _ θ hc hβ hθ p
  decomposition := fun z => by
    rw [← Fin.sum_univ_eq_sum_range (fun p => outerFinePiece m M D d c θ p z) (levels θ+1)]
    exact outerFinePiece_sum m M D d c θ z

theorem outerFineData_overlap (m : ℕ) (M : Node E) (D : Geometry F) (d : ℕ) (c θ : ℝ)
    (hc : 0<c) (hβ : 0<(D d []).width) (hθ : 1≤θ) (z : Joint E (Blocks m F)) :
    ((outerFineData m M D d c θ hc hβ hθ).activePieces z).card≤3 :=
  actual_outer_piece_overlap m M D d c θ hc hθ z

theorem outerFineData_carrier_trace (m : ℕ) (M : Node E) (D : Geometry F) (d : ℕ) (c θ : ℝ)
    (hc : 0<c) (hβ : 0<(D d []).width) (hθ : 1≤θ) (z : Joint E (Blocks m F)) :
    (outerFineData m M D d c θ hc hβ hθ).A z+(outerFineData m M D d c θ hc hβ hθ).r z=
      outerCarrier m M D d d z := by simp only [outerFineData,outerDeepestA,sub_add_cancel]

theorem outerFineData_zero (m : ℕ) (M : Node E) (D : Geometry F) (d : ℕ) (c θ : ℝ)
    (hc : 0<c) (hβ : 0<(D d []).width) (hθ : 1≤θ) :
    (outerFineData m M D d c θ hc hβ hθ).A 0=0 ∧
      (outerFineData m M D d c θ hc hβ hθ).r 0=0 := by
  simp [outerFineData,outerDeepestA,outerCarrier,outerFineFrontier,outerSelected,
    jointCarrier_zero,selectedFineFrontier_zero]

def outerFineNormal (m : ℕ) (M : Node E) (D : Geometry F) (d : ℕ) (c θ : ℝ)
    (hc : 0<c) (hβ : 0<(D d []).width) (hθ : 1≤θ) (s : ℕ) (i : Fin s) :
    ChiExtension.Full (Joint E (Blocks m F)) s → ℝ :=
  ChiExtension.fineTerm s i (outerFineData m M D d c θ hc hβ hθ)

theorem outerFineNormal_contDiff (m : ℕ) (M : Node E) (D : Geometry F) (d : ℕ) (c θ : ℝ)
    (hc : 0<c) (hβ : 0<(D d []).width) (hθ : 1≤θ) (s : ℕ) (i : Fin s) :
    ContDiff ℝ 3 (outerFineNormal m M D d c θ hc hβ hθ s i) := ChiExtension.fineTerm_contDiff s i _

theorem outerFineNormal_zero_trace (m : ℕ) (M : Node E) (D : Geometry F) (d : ℕ) (c θ : ℝ)
    (hc : 0<c) (hβ : 0<(D d []).width) (hθ : 1≤θ) (s : ℕ) (i : Fin s)
    (z : Joint E (Blocks m F)) :
    outerFineNormal m M D d c θ hc hβ hθ s i (pack z 0)=0 := ChiExtension.fineTerm_zero_trace s i _ z

theorem outerFineNormal_normal_gradient (m : ℕ) (M : Node E) (D : Geometry F) (d : ℕ) (c θ : ℝ)
    (hc : 0<c) (hβ : 0<(D d []).width) (hθ : 1≤θ) (s : ℕ) (i : Fin s)
    (z : Joint E (Blocks m F)) :
    HasGradientAt (fun q : ChiExtension.Normals s => outerFineNormal m M D d c θ hc hβ hθ s i (pack z q))
      (EuclideanSpace.single i (outerFineFrontier m M D d z)) 0 :=
  ChiExtension.fineTerm_normal_gradient s i _ z

end Bilevel.ChiOuter
