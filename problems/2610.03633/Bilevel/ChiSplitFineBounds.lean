import Bilevel.ChiSplitFlatProfileBounds

/-! Actual joint positive jets of source-only flattening. The selector variables
are independent predecessor coordinates and are included in every norm. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiSplitFine
open ChiBoundedChain

theorem flattened_positive_jet_bounds : ∃ C : ℝ,1≤C ∧
    ∀ (n : ℕ) (δ : ℝ),0<δ → δ≤1/16 → ∀ (j : Fin 3) (z : Latent n),
      ‖iteratedFDeriv ℝ (j.val+1) (flattened n δ) z‖≤C/δ^j.val := by
  obtain ⟨B,hB,hsel⟩ := selector_uniform_jet_bound
  obtain ⟨C,hC,hprofile⟩ := flat_profile_jet_bounds
  let S := 1+∑ j,B j
  have hS : 1≤S := le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ => hB j))
  have hS0 : 0≤S := by linarith only [hS]
  have hC0 : 0≤C := by linarith only [hC]
  have hbS (j : Fin 4) : B j≤S := by
    have hh := Finset.single_le_sum (fun l (_ : l∈Finset.univ) => hB l) (Finset.mem_univ j)
    dsimp [S]
    linarith only [hh]
  refine ⟨8*S*C,by nlinarith only [mul_le_mul hS hC (by norm_num : (0:ℝ)≤1) hS0],
    fun n δ hδ hs j z => ?_⟩
  have hδ1 : δ≤1 := by linarith only [hs]
  let b : ℕ → ℝ := fun k => if k=0 then C else C/δ^(k-1)
  have hp (k : ℕ) (hk : k≤3) (t : ℝ) : |iteratedDeriv k (flatProfile δ) t|≤b k :=
    hprofile δ hδ hδ1 ⟨k,by omega⟩ t
  have hb (k : ℕ) (hk : k≤j.val+1) : b k≤C/δ^j.val := by
    by_cases hk0 : k=0
    · subst k
      dsimp [b]
      apply (le_div_iff₀ (pow_pos hδ _)).mpr
      exact mul_le_of_le_one_right hC0 (pow_le_one₀ hδ.le hδ1)
    · simp only [b,if_neg hk0]
      exact div_le_div_of_nonneg_left hC0 (pow_pos hδ _)
        (pow_le_pow_of_le_one hδ.le hδ1 (by omega))
  have hh := selected_jet_bound n (flatProfile_contDiff δ) (fun _ => S) b (fun _ => hS0)
    (fun i w k hk => (hsel ⟨k,by omega⟩ n i w).trans (hbS _)) hp z (j.val+1) (by omega)
  apply hh.trans
  calc
    _≤∑ k ∈ Finset.range (j.val+1+1),((j.val+1).choose k:ℝ)*S*(C/δ^j.val) := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_left (hb (j.val+1-k) (by omega)) (by positivity)
    _=(2:ℝ)^(j.val+1)*S*(C/δ^j.val) := by
      fin_cases j <;> norm_num [Finset.sum_range_succ] <;> ring
    _≤8*S*(C/δ^j.val) := by
      have ht : (2:ℝ)^(j.val+1)≤8 := by fin_cases j <;> norm_num
      gcongr
    _=(8*S*C)/δ^j.val := by ring

end Bilevel.ChiSplitFine
