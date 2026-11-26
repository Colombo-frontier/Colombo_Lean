import Bilevel.PolishedLiteralChain

/-! The one-sided first-small-coordinate argument, with the actual penalty
handling coordinates below minus one. -/
noncomputable section
namespace Bilevel.PolishedLiteral
open ChiBoundedChain ZeroChainPotential

theorem coordinate_endgame (n : ℕ) (z : Space n) (j : Fin (n+1))
    (hj : z j < 1) (hprev : ∀ i : Fin (n+1), i.val < j.val → 1 ≤ z i) :
    gradient (value n) z j ≤ -1 := by
  by_cases hneg : z j ≤ -1
  · exact (gradient_le_penalty n z j).trans_eq (by rw [theta_one (by linarith)])
  have habs : |z j| ≤ 1 := abs_le.mpr ⟨by linarith, hj.le⟩
  revert habs hprev
  refine Fin.cases ?_ (fun i => ?_) j
  · intro _ habs
    have hφ : 1 ≤ phiSlope (z 0) := by
      simpa only [phi_deriv] using phi_deriv_ge_one (z 0) habs
    exact (gradient_first_le n z).trans (by linarith)
  · intro hprev habs
    have hi : 1 ≤ z i.castSucc := hprev i.castSucc (by simp)
    exact (gradient_succ_le_incoming z i).trans (edgeRight_le_neg_one _ _ hi habs)

theorem exists_gradient_coord_le_neg_one (n : ℕ) (z : Space n)
    (hlast : z (Fin.last n) < 1) :
    ∃ j : Fin (n+1), gradient (value n) z j ≤ -1 := by
  classical
  let s : Finset (Fin (n+1)) := Finset.univ.filter (fun j => z j < 1)
  have hs : s.Nonempty := ⟨Fin.last n, by simp [s, hlast]⟩
  let j := s.min' hs
  have hjmem : j ∈ s := Finset.min'_mem s hs
  have hj : z j < 1 := (Finset.mem_filter.mp hjmem).2
  refine ⟨j, coordinate_endgame n z j hj ?_⟩
  intro i hi
  by_contra h
  have himem : i ∈ s := by simp [s, lt_of_not_ge h]
  exact (not_lt_of_ge (Finset.min'_le s i himem)) hi

theorem endgame (n : ℕ) (z : Space n) (hlast : z (Fin.last n) < 1) :
    1 ≤ ‖gradient (value n) z‖ := by
  obtain ⟨j, hj⟩ := exists_gradient_coord_le_neg_one n z hlast
  have hc : |gradient (value n) z j| ≤ ‖gradient (value n) z‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (gradient (value n) z) j
  have ha := neg_abs_le (gradient (value n) z j)
  linarith

def chain (n : ℕ) (ℓ h : ℝ) : Space n → ℝ :=
  ZeroChainResidualScaled.scaled (value n) (ℓ*h^2) h

theorem chain_contDiff (n : ℕ) (ℓ h : ℝ) (k : ℕ) : ContDiff ℝ k (chain n ℓ h) :=
  contDiff_const.mul ((value_contDiff n k).comp (contDiff_const.smul contDiff_id))

theorem chain_gradient (n : ℕ) (ℓ h : ℝ) (hh : 0 < h) (z : Space n) :
    gradient (chain n ℓ h) z = (ℓ*h) • gradient (value n) (h⁻¹ • z) := by
  rw [chain, ZeroChainResidualScaled.scaled_gradient
    ((value_contDiff n 1).differentiable (by norm_num))]
  congr 1
  field_simp
  ring

theorem chain_gradient_nonpos (n : ℕ) (ℓ h : ℝ) (hℓ : 0 ≤ ℓ) (hh : 0 < h)
    (z : Space n) (j : Fin (n+1)) : gradient (chain n ℓ h) z j ≤ 0 := by
  rw [chain_gradient n ℓ h hh, PiLp.smul_apply, smul_eq_mul]
  exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hℓ hh.le) (gradient_coord_nonpos n _ j)

theorem chain_endgame (n : ℕ) (ℓ h : ℝ) (hℓ : 0 ≤ ℓ) (hh : 0 < h)
    (z : Space n) (hlast : z (Fin.last n) < h) : ℓ*h ≤ ‖gradient (chain n ℓ h) z‖ := by
  have hz : (h⁻¹ • z) (Fin.last n) < 1 := by
    simp only [PiLp.smul_apply, smul_eq_mul]
    exact (inv_mul_lt_iff₀ hh).mpr (by simpa using hlast)
  have hm := mul_le_mul_of_nonneg_left (endgame n (h⁻¹ • z) hz) (mul_nonneg hℓ hh.le)
  simpa only [chain_gradient n ℓ h hh, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hℓ hh.le), mul_one] using hm

end Bilevel.PolishedLiteral
