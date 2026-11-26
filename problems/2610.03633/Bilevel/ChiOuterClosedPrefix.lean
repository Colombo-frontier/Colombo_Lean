import Bilevel.ChiVirtualMacroValues
import Bilevel.ChiOuterReleaseCorrection

/-! Prefix locality of the actual one-sided macro chain after its signed
release correction. This is the cancellation that prevents the exact upper
oracle from disclosing a macro frontier before a successful lower sample. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiOuter
open ChiBoundedChain ChiPrefixEvaluation ZeroChainPotential

def incoming (n : ℕ) (i : Fin (n+1)) (z : Space n) : ℝ :=
  Fin.cases (-phi (z 0)) (fun k => edge (z k.castSucc) (z k.succ)) i

def closedValue (n : ℕ) (q : Fin (n+1) → ℝ) (z : Space n) : ℝ :=
  value n z+∑ i : Fin (n+1),residualTerm n i z*(q i-1)

theorem value_sum_incoming (n : ℕ) (z : Space n) :
    value n z=(∑ i : Fin (n+1),incoming n i z)+∑ i : Fin (n+1),penalty (z i) := by
  rw [Fin.sum_univ_succ]
  rfl

theorem residualTerm_eq_incoming (n : ℕ) (i : Fin (n+1)) (z : Space n) :
    residualTerm n i z=incoming n i z*tailMask i z := by
  refine Fin.cases ?_ (fun k => ?_) i
  · simp only [residualTerm,selector,incoming,Fin.cases_zero]
    ring
  · simp only [residualTerm,selector,incoming,Fin.cases_succ,edge]
    ring

theorem selector_prefix_value (n r : ℕ) (i : Fin (n+1)) (z : Space n)
    (hz : ∀ k : Fin (n+1),r≤k.val → |z k|≤1/4) :
    selector n i z=selector n i (retain n r z) :=
  value_eq_retain _ ((selector_contDiff n 3 i).differentiable (by norm_num))
    (fun w hw k hk => outer_selector_gradient_small n i k w (hw k hk)) z hz

theorem incoming_prefix_value (n r : ℕ) (i : Fin (n+1)) (hi : i.val<r) (z : Space n) :
    incoming n i z=incoming n i (retain n r z) := by
  revert hi
  refine Fin.cases ?_ (fun k => ?_) i
  · intro hi
    simp only [incoming,Fin.cases_zero,retain_apply,if_pos hi]
  · intro hi
    have hk : k.castSucc.val<r := by simp only [Fin.val_succ] at hi;exact (Nat.lt_succ_self _).trans hi
    simp only [incoming,Fin.cases_succ,retain_apply,if_pos hi,if_pos hk]

theorem closedValue_prefix_value (n r : ℕ) (q : Fin (n+1) → ℝ)
    (hq : ∀ i : Fin (n+1),r≤ i.val → q i=0) (z : Space n)
    (hz : ∀ k : Fin (n+1),r≤k.val → |z k|≤1/4) :
    closedValue n q z=closedValue n q (retain n r z) := by
  have hr : ∀ k : Fin (n+1),r≤k.val → |retain n r z k|≤1/4 := by
    intro k hk
    rw [retain_apply,if_neg (by omega)]
    norm_num
  have hsum (w : Space n) : closedValue n q w=
      (∑ i : Fin (n+1),(incoming n i w+residualTerm n i w*(q i-1)))+
        ∑ i : Fin (n+1),penalty (w i) := by
    simp only [closedValue,value_sum_incoming,Finset.sum_add_distrib]
    ring
  rw [hsum,hsum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i.val<r
    · rw [incoming_prefix_value n r i hi z]
      simp only [residualTerm,selector_prefix_value n r i z hz,retain_apply,if_pos hi]
    · have hil : r≤ i.val := by omega
      have hz0 (w : Space n) (hw : ∀ k : Fin (n+1),r≤k.val → |w k|≤1/4) :
          incoming n i w+residualTerm n i w*(q i-1)=0 := by
        rw [residualTerm_eq_incoming,tailMask_one_of_small i w
          (fun k hik => hw k (hil.trans hik)),hq i hil]
        ring
      rw [hz0 z hz,hz0 _ hr]
  · apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i.val<r
    · rw [retain_apply,if_pos hi]
    · rw [penalty_flat (by linarith [(abs_le.mp (hz i (by omega))).1]),
        penalty_flat (by linarith [(abs_le.mp (hr i (by omega))).1])]

def closedChain (n : ℕ) (ell h : ℝ) (q : Fin (n+1) → ℝ) (z : Space n) : ℝ :=
  (ell*h^2)*closedValue n q (h⁻¹ • z)

theorem closedChain_prefix_value (n r : ℕ) (ell h : ℝ) (hh : 0<h)
    (q : Fin (n+1) → ℝ) (hq : ∀ i : Fin (n+1),r≤ i.val → q i=0) (z : Space n)
    (hz : ∀ k : Fin (n+1),r≤k.val → |z k|≤h/4) :
    closedChain n ell h q z=closedChain n ell h q (retain n r z) := by
  unfold closedChain
  rw [closedValue_prefix_value n r q hq _
    (fun k hk => ZeroChainResidualScaled.scaled_coordinate_small h hh z k (hz k hk)),map_smul]

end Bilevel.ChiOuter
