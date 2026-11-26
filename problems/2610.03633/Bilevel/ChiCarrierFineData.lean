import Bilevel.ChiCarrierFineSupport
import Bilevel.ChiCarrierBlockSlice

/-! The actual ancestor-selected finite decomposition as a normal-coupling
data object. The constants mu=L=1 below are unused bookkeeping for coupling
APIs; this module makes no lower-objective conditioning assertion. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiCarrier
open ChiBoundedChain ChiRecursive ZeroChainSchedule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem jointCarrier_zero (m : ℕ) (D : Geometry E) (d j : ℕ) (I : List ℕ) (k : ℕ) :
    jointCarrier m D d j I k 0=0 := by
  induction d generalizing j I k with
  | zero => cases k <;> simp [jointCarrier,selectedCarrier,padded]
  | succ d ih =>
    cases k with
    | zero =>
      simp only [jointCarrier,selectedCarrier,padded,map_zero,Node.release_zero,mul_zero,
        Finset.sum_const_zero,add_zero,Node.H_zero_eq_residual_sum,sub_self]
    | succ k =>
      change (∑ i : Fin ((D j I).n+1),jointSelector m j (D j I) i 0*
        jointCarrier m D d (j+1) (child I i.val) k 0)=0
      simp only [ih,mul_zero,Finset.sum_const_zero]

theorem jointFineFrontier_zero (m j : ℕ) (D : Node E) : jointFineFrontier m j D 0=0 := by
  simp [jointFineFrontier,ChiFine.frontier,ZeroChainResidualScaled.scaled,Node.coordinates_zero,
    centeredResidual_zero]

theorem selectFamily_zero (m : ℕ) (D : Geometry E) (leaf : ℕ → List ℕ → Blocks m E → ℝ)
    (hzero : ∀ j I,leaf j I 0=0) (d j : ℕ) (I : List ℕ) : selectFamily m D leaf d j I 0=0 := by
  induction d generalizing j I with
  | zero => exact hzero j I
  | succ d ih => simp only [selectFamily,ih,mul_zero,Finset.sum_const_zero]

theorem selectedFineFrontier_zero (m : ℕ) (D : Geometry E) (d j : ℕ) (I : List ℕ) :
    selectedFineFrontier m D d j I 0=0 :=
  selectFamily_zero m D _ (fun j I => jointFineFrontier_zero m j (D j I)) d j I

def fineData (m : ℕ) (D : Geometry E) (d j : ℕ) (I : List ℕ) (c θ : ℝ)
    (hc : 0<c) (hβ : 0<(D (j+d) []).width) (hθ : 1≤θ) : CompensatedMean.Data (E:=Blocks m E) where
  μ := 1
  L := 1
  J := levels θ
  r := selectedFineFrontier m D d j I
  A := fun x => jointCarrier m D d j I d x-selectedFineFrontier m D d j I x
  e := selectedFinePiece m D d j I c θ
  w := width c (D (j+d) []).width θ
  r_smooth := selectedFineFrontier_contDiff m D d j I
  A_smooth := (jointCarrier_contDiff m D d j I d 3).sub (selectedFineFrontier_contDiff m D d j I)
  e_smooth := selectedFinePiece_contDiff m D d j I c θ
  w_pos := fun p _ => width_pos c _ θ hc hβ hθ p
  decomposition := fun x => by
    rw [← Fin.sum_univ_eq_sum_range (fun p => selectedFinePiece m D d j I c θ p x) (levels θ+1)]
    exact selectedFinePiece_sum m D d j I c θ x

theorem fineData_overlap (m : ℕ) (D : Geometry E) (d j : ℕ) (I : List ℕ) (c θ : ℝ)
    (hc : 0<c) (hβ : 0<(D (j+d) []).width) (hθ : 1≤θ) (x : Blocks m E) :
    ((fineData m D d j I c θ hc hβ hθ).activePieces x).card≤3 :=
  actual_selected_piece_overlap m D d j I c θ hc hθ x

theorem fineData_carrier_trace (m : ℕ) (D : Geometry E) (d j : ℕ) (I : List ℕ) (c θ : ℝ)
    (hc : 0<c) (hβ : 0<(D (j+d) []).width) (hθ : 1≤θ) (x : Blocks m E) :
    (fineData m D d j I c θ hc hβ hθ).A x+(fineData m D d j I c θ hc hβ hθ).r x=
      jointCarrier m D d j I d x := by simp only [fineData,sub_add_cancel]

theorem fineData_zero (m : ℕ) (D : Geometry E) (d j : ℕ) (I : List ℕ) (c θ : ℝ)
    (hc : 0<c) (hβ : 0<(D (j+d) []).width) (hθ : 1≤θ) :
    (fineData m D d j I c θ hc hβ hθ).A 0=0 ∧ (fineData m D d j I c θ hc hβ hθ).r 0=0 := by
  simp [fineData,jointCarrier_zero,selectedFineFrontier_zero]

end Bilevel.ChiCarrier
