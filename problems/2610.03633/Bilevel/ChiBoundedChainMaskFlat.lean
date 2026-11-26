import Bilevel.ChiBoundedChainProfileBounds

/-! Flat boundary jets and uniform scalar mask bounds for the actual revised C-infinity profiles. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiBoundedChain

theorem coordinateCutoff_flat_inner (j : ℕ) (hj : j ≤ 3) (t : ℝ) (ht : |t| ≤ 1/4) :
    iteratedDeriv j coordinateCutoff t = 0 := by
  by_cases hj0 : j = 0
  · subst j
    simpa only [iteratedDeriv_zero] using coordinateCutoff_zero ht
  · exact ZeroChainResidualCutoffs.iteratedDeriv_zero_of_constant_on coordinateCutoff_contDiff
      (uniqueDiffOn_Icc (by norm_num : -(1/4:ℝ) < 1/4))
      (fun x hx => coordinateCutoff_zero (abs_le.mpr hx)) j (by omega) hj t (abs_le.mp ht)

theorem coordinateCutoff_flat_outer (j : ℕ) (hj0 : 1 ≤ j) (hj : j ≤ 3)
    (t : ℝ) (ht : 1/2 ≤ |t|) : iteratedDeriv j coordinateCutoff t = 0 := by
  rcases le_total 0 t with hpos | hneg
  · apply ZeroChainResidualCutoffs.iteratedDeriv_zero_of_constant_on coordinateCutoff_contDiff
      (uniqueDiffOn_Ici (1/2)) (c:=1)
      (fun x hx => coordinateCutoff_one (by
        change (1/2:ℝ) ≤ x at hx
        simpa only [abs_of_nonneg (by linarith : 0 ≤ x)] using hx))
      j hj0 hj t
    simpa only [abs_of_nonneg hpos] using ht
  · apply ZeroChainResidualCutoffs.iteratedDeriv_zero_of_constant_on coordinateCutoff_contDiff
      (uniqueDiffOn_Iic (-(1/2))) (c:=1)
      (fun x hx => coordinateCutoff_one (by
        change x ≤ -(1/2:ℝ) at hx
        rw [abs_of_nonpos (by linarith : x ≤ 0)]; linarith))
      j hj0 hj t
    rw [abs_of_nonpos hneg] at ht
    change t ≤ -(1/2:ℝ)
    linarith

theorem energyCutoff_flat_right (j : ℕ) (hj : j ≤ 3) (s : ℝ) (hs : 1 ≤ s) :
    iteratedDeriv j energyCutoff s = 0 := by
  by_cases hj0 : j = 0
  · subst j
    simpa only [iteratedDeriv_zero] using energyCutoff_zero hs
  · exact ZeroChainResidualCutoffs.iteratedDeriv_zero_of_constant_on energyCutoff_contDiff (uniqueDiffOn_Ici 1)
      (fun _ ht => energyCutoff_zero ht) j (by omega) hj s hs

theorem energyCutoff_flat_left (j : ℕ) (hj0 : 1 ≤ j) (hj : j ≤ 3)
    (s : ℝ) (hs : s ≤ 1/4) : iteratedDeriv j energyCutoff s = 0 :=
  ZeroChainResidualCutoffs.iteratedDeriv_zero_of_constant_on energyCutoff_contDiff (uniqueDiffOn_Iic (1/4))
    (fun _ ht => energyCutoff_one ht) j hj0 hj s hs

theorem coordinateCutoff_deriv_compactSupport : HasCompactSupport (deriv coordinateCutoff) := by
  apply SmallGapProfileBounds.compactSupport_of_tail (1/2)
  intro t ht
  simpa only [iteratedDeriv_one] using coordinateCutoff_flat_outer 1 (by norm_num) (by norm_num) t ht

theorem energyCutoff_deriv_compactSupport : HasCompactSupport (deriv energyCutoff) := by
  apply SmallGapProfileBounds.compactSupport_of_tail 1
  intro t ht
  rcases le_total 0 t with hp | hn
  · simpa only [iteratedDeriv_one] using energyCutoff_flat_right 1 (by norm_num) t
      (by simpa only [abs_of_nonneg hp] using ht)
  · simpa only [iteratedDeriv_one] using energyCutoff_flat_left 1 (by norm_num) (by norm_num) t
      (by rw [abs_of_nonpos hn] at ht; linarith)

theorem cutoff_common_bound : ∃ C : ℝ, 1 ≤ C ∧ ∀ j : Fin 4, ∀ t,
    |iteratedDeriv j.val coordinateCutoff t| ≤ C ∧ |iteratedDeriv j.val energyCutoff t| ≤ C := by
  have he (j : Fin 4) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t,
      |iteratedDeriv j.val coordinateCutoff t| ≤ C ∧ |iteratedDeriv j.val energyCutoff t| ≤ C := by
    obtain ⟨A,hA,ha⟩ := ZeroChainResidualCutoffs.plateau_profile_bound coordinateCutoff coordinateCutoff_contDiff
      coordinateCutoff_range coordinateCutoff_deriv_compactSupport j.val (by omega)
    obtain ⟨B,hB,hb⟩ := ZeroChainResidualCutoffs.plateau_profile_bound energyCutoff energyCutoff_contDiff
      energyCutoff_range energyCutoff_deriv_compactSupport j.val (by omega)
    refine ⟨A+B, by positivity, fun t => ⟨?_, ?_⟩⟩
    · exact (ha t).trans (le_add_of_nonneg_right hB)
    · exact (hb t).trans (le_add_of_nonneg_left hA)
  choose C hC hb using he
  refine ⟨1+∑ j, C j, le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ => hC j)), fun j t => ⟨?_, ?_⟩⟩
  all_goals have hj : C j ≤ ∑ k, C k := Finset.single_le_sum (fun k _ => hC k) (Finset.mem_univ j)
  · exact (hb j t).1.trans (by linarith)
  · exact (hb j t).2.trans (by linarith)


end Bilevel.ChiBoundedChain
