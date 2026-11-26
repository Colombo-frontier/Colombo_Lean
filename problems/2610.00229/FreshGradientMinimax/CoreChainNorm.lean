import FreshGradientMinimax.CoreChainBarrier

/-! A stronger-than-requested gradient norm bound for (22), obtained from
the actual sparse gradient: each coordinate has at most one incoming and
one outgoing adjacent-coordinate contribution. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators

theorem sum_injective_fiber_le {I J : Type*} [Fintype I] [DecidableEq J]
    (f : I → J) (hf : Function.Injective f) (w : I → ℝ) (j : J) {C : ℝ}
    (hC : 0 ≤ C) (hw : ∀ i, w i ≤ C) : (∑ i, if f i = j then w i else 0) ≤ C := by
  classical
  by_cases h : ∃ i, f i = j
  · obtain ⟨i, hi⟩ := h
    calc
      _ = w i := by
        rw [Finset.sum_eq_single i]
        · rw [if_pos hi]
        · intro k _ hki
          apply if_neg
          intro hk
          exact hki (hf (hk.trans hi.symm))
        · simp
      _ ≤ C := hw i
  · have hi : ∀ i, f i ≠ j := by simpa only [not_exists] using h
    simp only [if_neg (hi _), Finset.sum_const_zero]
    exact hC

theorem coreChainGradient_coordinate_bound {n : ℕ} (u : Euclid (n + 1)) (j : Fin (n + 1)) :
    |coreChainGradient u j| ≤ 103 := by
  classical
  have h1 := sum_injective_fiber_le (fun e : Fin n => e.castSucc) (Fin.castSucc_injective n)
    (fun e => -coreLinkTermD1 (u e.castSucc) (u e.succ)) j (by norm_num : (0 : ℝ) ≤ 96)
    (fun e => (neg_le_abs _).trans (coreLinkTermD1_bound _ _))
  have h2 := sum_injective_fiber_le (fun e : Fin n => e.succ) (Fin.succ_injective n)
    (fun e => -coreLinkTermD2 (u e.castSucc) (u e.succ)) j (by norm_num : (0 : ℝ) ≤ 6)
    (fun e => (neg_le_abs _).trans (coreLinkTermD2_bound _ _))
  have he1 : (∑ e : Fin n, if e.castSucc = j then -coreLinkTermD1 (u e.castSucc) (u e.succ) else 0) =
      -(∑ e : Fin n, if e.castSucc = j then coreLinkTermD1 (u e.castSucc) (u e.succ) else 0) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro e _
    split_ifs <;> simp
  have he2 : (∑ e : Fin n, if e.succ = j then -coreLinkTermD2 (u e.castSucc) (u e.succ) else 0) =
      -(∑ e : Fin n, if e.succ = j then coreLinkTermD2 (u e.castSucc) (u e.succ) else 0) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro e _
    split_ifs <;> simp
  rw [he1] at h1
  rw [he2] at h2
  have hs : -(if (0 : Fin (n + 1)) = j then -coreDensity (u 0) else 0) ≤ 1 := by
    split_ifs
    · simpa only [neg_neg] using coreDensity_le_one (u 0)
    · norm_num
  rw [abs_of_nonpos (coreChainGradient_nonpos u j), coreChainGradient_apply, Finset.sum_add_distrib]
  linarith only [h1, h2, hs]

theorem coreChainGradient_norm_sq {n : ℕ} (u : Euclid (n + 1)) :
    ‖coreChainGradient u‖ ^ 2 ≤ 103 ^ 2 * (n + 1 : ℝ) := by
  rw [euclid_norm_sq]
  calc
    _ ≤ ∑ _j : Fin (n + 1), (103 : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      have h := pow_le_pow_left₀ (abs_nonneg _) (coreChainGradient_coordinate_bound u j) 2
      simpa only [sq_abs] using h
    _ = _ := by simp; ring

theorem coreChain_gradient_norm {n : ℕ} (u : Euclid (n + 1)) :
    ‖gradient coreChain u‖ ≤ 103 * Real.sqrt (n + 1 : ℝ) := by
  rw [coreChain_gradient]
  have hs := Real.sq_sqrt (show 0 ≤ (n + 1 : ℝ) by positivity)
  have hn := coreChainGradient_norm_sq u
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  nlinarith only [hn, hs]

theorem coreChain_gradient_original_bound {n : ℕ} (u : Euclid (n + 1)) :
    ‖gradient coreChain u‖ ≤ 10 ^ 6 * Real.sqrt (n + 1 : ℝ) := by
  have h := coreChain_gradient_norm u
  have hr := Real.sqrt_nonneg (n + 1 : ℝ)
  nlinarith

end FreshGradientMinimax
