import FreshGradientMinimax.CoreChainGradient

/-! The true-gradient barrier in Lemma C.1: if the last coordinate is small,
one coordinate of magnitude at most one has derivative at most -exp(-1/2). -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

theorem coreChainGradient_barrier_at {n : ℕ} (u : Euclid (n + 1)) (j : Fin (n + 1))
    (hj : |u j| ≤ 1) (hprev : ∀ k : Fin (n + 1), k < j → 1 ≤ |u k|) :
    coreChainGradient u j ≤ -Real.exp (-(1 / 2 : ℝ)) := by
  cases j using Fin.cases with
  | zero =>
    have h1 := coreChainGradient_seed_le u
    have h2 := coreDensity_lower_on_unit hj
    linarith
  | succ i =>
    have hp := hprev i.castSucc (by change i.val < i.val + 1; omega)
    exact (coreChainGradient_incoming_le u i).trans (coreLinkTermD2_barrier hp hj)

theorem finite_first_small_coordinate {n : ℕ} (u : Fin (n + 1) → ℝ)
    (hlast : |u (Fin.last n)| ≤ 1 / 4) :
    ∃ j : Fin (n + 1), |u j| ≤ 1 ∧ ∀ k : Fin (n + 1), k < j → 1 ≤ |u k| := by
  classical
  let s := Finset.univ.filter (fun j : Fin (n + 1) => |u j| < 1)
  have hs : s.Nonempty := by
    refine ⟨Fin.last n, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    linarith
  refine ⟨s.min' hs, (Finset.mem_filter.mp (Finset.min'_mem s hs)).2.le, ?_⟩
  intro k hk
  by_contra h
  have hkm : k ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_not_ge h⟩
  exact (not_lt_of_ge (Finset.min'_le s k hkm)) hk

theorem coreChain_coordinate_barrier {n : ℕ} (u : Euclid (n + 1))
    (hlast : |u (Fin.last n)| ≤ 1 / 4) :
    ∃ j : Fin (n + 1), |u j| ≤ 1 ∧ gradient coreChain u j ≤ -Real.exp (-(1 / 2 : ℝ)) := by
  obtain ⟨j, hj, hp⟩ := finite_first_small_coordinate (fun i => u i) hlast
  refine ⟨j, hj, ?_⟩
  rw [coreChain_gradient]
  exact coreChainGradient_barrier_at u j hj hp

theorem coreChain_gradient_barrier {n : ℕ} (u : Euclid (n + 1))
    (hlast : |u (Fin.last n)| ≤ 1 / 4) : Real.exp (-(1 / 2 : ℝ)) ≤ ‖gradient coreChain u‖ := by
  obtain ⟨j, _, hj⟩ := coreChain_coordinate_barrier u hlast
  have hn := PiLp.norm_apply_le (gradient coreChain u) j
  rw [Real.norm_eq_abs] at hn
  have ha := neg_le_abs (gradient coreChain u j)
  linarith

end FreshGradientMinimax
