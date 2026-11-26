import Bilevel.ChiBoundedChainActiveCertificate

/-! Numerical scalar jet bounds for the actual receiver gates, including
weighted positive-order jets. These weighted bounds control the affine factor
in the positive receiver without losing a factor hp/h. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiBoundedChain.ReceiverJets

def profile (i : Fin 3) : ℝ → ℝ := ![receiverGate,positiveTail,negativeTail] i

theorem profile_contDiff (i : Fin 3) : ContDiff ℝ 3 (profile i) := by
  fin_cases i
  · exact receiverGate_contDiff
  · exact positiveTail_contDiff
  · exact negativeTail_contDiff

theorem profile_range (i : Fin 3) (t : ℝ) : 0≤profile i t ∧ profile i t≤1 := by
  fin_cases i
  · exact receiverGate_range t
  · exact positiveTail_range t
  · exact negativeTail_range t

theorem profile_flat_left (i : Fin 3) (j : ℕ) (hj0 : 1≤j) (hj3 : j≤3)
    (t : ℝ) (ht : t≤0) : iteratedDeriv j (profile i) t=0 := by
  fin_cases i
  · exact ZeroChainResidualCutoffs.iteratedDeriv_zero_of_constant_on receiverGate_contDiff
      (uniqueDiffOn_Iic 0) (fun x hx => receiverGate_zero (by have hh : x≤0 := hx;linarith)) j hj0 hj3 t ht
  · exact ZeroChainResidualCutoffs.iteratedDeriv_zero_of_constant_on positiveTail_contDiff
      (uniqueDiffOn_Iic 0) (fun x hx => positiveTail_one (by have hh : x≤0 := hx;linarith)) j hj0 hj3 t ht
  · exact ZeroChainResidualCutoffs.iteratedDeriv_zero_of_constant_on negativeTail_contDiff
      (uniqueDiffOn_Iic 0) (fun x hx => negativeTail_one (by have hh : x≤0 := hx;linarith)) j hj0 hj3 t ht

theorem profile_flat_right (i : Fin 3) (j : ℕ) (hj0 : 1≤j) (hj3 : j≤3)
    (t : ℝ) (ht : 3≤t) : iteratedDeriv j (profile i) t=0 := by
  fin_cases i
  · exact ZeroChainResidualCutoffs.iteratedDeriv_zero_of_constant_on receiverGate_contDiff
      (uniqueDiffOn_Ici 3) (fun x hx => receiverGate_one (by have hh : 3≤x := hx;linarith)) j hj0 hj3 t ht
  · exact ZeroChainResidualCutoffs.iteratedDeriv_zero_of_constant_on positiveTail_contDiff
      (uniqueDiffOn_Ici 3) (fun _ hx => positiveTail_zero hx) j hj0 hj3 t ht
  · exact ZeroChainResidualCutoffs.iteratedDeriv_zero_of_constant_on negativeTail_contDiff
      (uniqueDiffOn_Ici 3) (fun x hx => negativeTail_zero (by have hh : 3≤x := hx;linarith)) j hj0 hj3 t ht

theorem profile_flat_outer (i : Fin 3) (j : ℕ) (hj0 : 1≤j) (hj3 : j≤3)
    (t : ℝ) (ht : 3≤|t|) : iteratedDeriv j (profile i) t=0 := by
  rcases le_total 0 t with hp|hn
  · exact profile_flat_right i j hj0 hj3 t (by simpa only [abs_of_nonneg hp] using ht)
  · exact profile_flat_left i j hj0 hj3 t hn

theorem profile_deriv_compactSupport (i : Fin 3) : HasCompactSupport (deriv (profile i)) := by
  apply SmallGapProfileBounds.compactSupport_of_tail 3
  intro t ht
  simpa only [iteratedDeriv_one] using profile_flat_outer i 1 (by norm_num) (by norm_num) t ht

theorem profiles_common_bound : ∃ B : ℝ,1≤B ∧
    (∀ (i : Fin 3) (j : Fin 4) (t : ℝ),|iteratedDeriv j.val (profile i) t|≤B) ∧
    (∀ (i : Fin 3) (j : ℕ),1≤j → j≤3 → ∀ t,|t*iteratedDeriv j (profile i) t|≤3*B) := by
  have he (i : Fin 3) (j : Fin 4) := ZeroChainResidualCutoffs.plateau_profile_bound
    (profile i) (profile_contDiff i) (profile_range i) (profile_deriv_compactSupport i) j.val (show j.val≤3 by omega)
  choose C hC hc using he
  let B := 1+∑ i : Fin 3,∑ j : Fin 4,C i j
  have hsum : 0≤∑ i : Fin 3,∑ j : Fin 4,C i j :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hC i j))
  have hB : 1≤B := by unfold B;linarith
  have hb (i : Fin 3) (j : Fin 4) (t : ℝ) : |iteratedDeriv j.val (profile i) t|≤B := by
    have h₁ := Finset.single_le_sum (fun k (_ : k∈Finset.univ) => hC i k) (Finset.mem_univ j)
    have h₂ := Finset.single_le_sum (f:=fun k : Fin 3 => ∑ l : Fin 4,C k l) (fun k (_ : k∈Finset.univ) =>
      Finset.sum_nonneg (fun l _ => hC k l)) (Finset.mem_univ i)
    exact (hc i j t).trans (by unfold B;linarith)
  refine ⟨B,hB,hb,fun i j hj0 hj3 t => ?_⟩
  by_cases ht : 3≤|t|
  · rw [profile_flat_outer i j hj0 hj3 t ht,mul_zero,abs_zero]
    linarith
  · rw [abs_mul]
    exact mul_le_mul (le_of_lt (lt_of_not_ge ht)) (hb i ⟨j,by omega⟩ t) (abs_nonneg _) (by norm_num)

end Bilevel.ChiBoundedChain.ReceiverJets
