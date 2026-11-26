import Smoothness2601.ExtensiveChain

/-! Actual source chain nonstationarity. The amplitude is calibrated by the
proved dimension-free frontier gradient bound; this slightly larger absolute
constant is sufficient for the existential hard construction. -/
noncomputable section
namespace Smoothness2601.ExtensiveChain
open Cutoffs ChainProfiles Finset Filter
open scoped BigOperators RealInnerProductSpace Topology ContDiff

theorem frontier_contDiff {ι : Type*} [Fintype ι] [LinearOrder ι] :
    ContDiff ℝ ∞ (Cutoffs.frontier (ι := ι)) := by
  unfold Cutoffs.frontier BoundedFrontier.frontier BoundedFrontier.summand BoundedFrontier.prefixValue
  apply ContDiff.neg
  apply ContDiff.sum
  intro i _
  apply ContDiff.mul
  · apply contDiff_prod
    intro j _
    exact (gate_contDiff ⊤).comp (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff
  · exact (bump_contDiff ⊤).comp (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff

def chain (M : ℝ) {n : ℕ} (z : Space n) : ℝ := extensive M z + Cutoffs.frontier z

theorem chain_contDiff (M : ℝ) (n : ℕ) : ContDiff ℝ ∞ (chain M (n := n)) :=
  (extensive_contDiff M n).add frontier_contDiff

theorem chain_gradient (M : ℝ) {n : ℕ} (z : Space n) :
    gradient (chain M) z = gradient (extensive M) z + gradient Cutoffs.frontier z := by
  apply HasGradientAt.gradient
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert (extensive_hasFDerivAt M z).differentiableAt.hasGradientAt.hasFDerivAt.add
    (actual_frontier_differentiable z).1.hasGradientAt.hasFDerivAt using 1
  ext v
  simp [InnerProductSpace.toDual_apply,inner_add_left]

def coordinateLine {n : ℕ} (z : Space n) (k : Fin (n + 1)) (t : ℝ) : Space n :=
  z + t • EuclideanSpace.single k 1

theorem coordinateLine_self {n : ℕ} (z : Space n) (k : Fin (n + 1)) (t : ℝ) :
    coordinateLine z k t k = z k + t := by simp [coordinateLine]

theorem coordinateLine_other {n : ℕ} (z : Space n) (k i : Fin (n + 1)) (t : ℝ)
    (hi : i ≠ k) : coordinateLine z k t i = z i := by
  simp [coordinateLine, EuclideanSpace.single_apply, hi, Ne.symm hi]

theorem frontier_coordinateLine_near {n : ℕ} (z : Space n) (k : Fin (n + 1))
    (hfirst : ∀ j : Fin (n + 1), j < k → 1 ≤ |z j|) {t : ℝ}
    (ht : |z k + t| < 1/8) :
    Cutoffs.frontier (coordinateLine z k t) = -(z k + t) := by
  classical
  unfold Cutoffs.frontier BoundedFrontier.frontier
  have hmain : BoundedFrontier.summand gate bump k (coordinateLine z k t) = z k + t := by
    unfold BoundedFrontier.summand BoundedFrontier.prefixValue
    have hp : (∏ j ∈ BoundedFrontier.prefixSet k, gate (coordinateLine z k t j)) = 1 := by
      apply Finset.prod_eq_one
      intro j hj
      have hjk := BoundedFrontier.mem_prefixSet.mp hj
      rw [coordinateLine_other z k j t (ne_of_lt hjk)]
      exact gate_one (hfirst j hjk)
    rw [hp, one_mul, coordinateLine_self, bump_identity ht.le]
  rw [Finset.sum_eq_single k, hmain]
  · intro i _ hik
    rcases lt_or_gt_of_ne hik with hi | hi
    · have hb : bump (coordinateLine z k t i) = 0 := by
        rw [coordinateLine_other z k i t hik]
        exact bump_zero (by have := hfirst i hi; linarith)
      simp [BoundedFrontier.summand, hb]
    · have hg : gate (coordinateLine z k t k) = 0 := by
        rw [coordinateLine_self]
        exact gate_zero (by linarith)
      simp [BoundedFrontier.summand, BoundedFrontier.prefix_zero_of_earlier hi hg]
  · simp

theorem frontier_gradient_coordinate_near {n : ℕ} (z : Space n) (k : Fin (n + 1))
    (hfirst : ∀ j : Fin (n + 1), j < k → 1 ≤ |z j|) (hk : |z k| < 1/8) :
    gradient Cutoffs.frontier z k = -1 := by
  have hline : HasDerivAt (coordinateLine z k) (EuclideanSpace.single k 1) 0 := by
    simpa only [coordinateLine,id_eq,one_smul] using
      ((hasDerivAt_id (0 : ℝ)).smul_const (EuclideanSpace.single k 1)).const_add z
  have hb := (actual_frontier_differentiable z).1.hasFDerivAt
  have hz : coordinateLine z k 0 = z := by simp [coordinateLine]
  have hc := (show HasFDerivAt Cutoffs.frontier (fderiv ℝ Cutoffs.frontier z)
    (coordinateLine z k 0) from hz.symm ▸ hb).comp_hasDerivAt 0 hline
  have heq : (fun t : ℝ => Cutoffs.frontier (coordinateLine z k t)) =ᶠ[𝓝 0]
      (fun t => -(z k + t)) := by
    have hn : ∀ᶠ t : ℝ in 𝓝 0, |z k + t| < 1/8 := by
      exact (isOpen_lt ((continuous_const.add continuous_id).abs) continuous_const).mem_nhds (by simpa using hk)
    exact hn.mono fun t ht => frontier_coordinateLine_near z k hfirst ht
  have hm : HasDerivAt (fun t : ℝ => -(z k + t)) (-1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_add (z k)).neg
  have hh := hc.unique (hm.congr_of_eventuallyEq heq)
  rw [gradient_coordinate_of_hasFDerivAt hb k]
  exact hh

theorem frontier_gradient_coordinate_le {n : ℕ} (z : Space n) (k : Fin (n + 1)) :
    gradient Cutoffs.frontier z k ≤ frontierGradientBound := by
  have hnorm : |gradient Cutoffs.frontier z k| ≤ ‖gradient Cutoffs.frontier z‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (gradient Cutoffs.frontier z) k
  exact (le_abs_self _).trans (hnorm.trans (actual_frontier_bounds z).2.1)

/-- First unrevealed coordinate has a gradient component at most -1. -/
theorem chain_frontier_nonstationary {M : ℝ} (hM : 0 ≤ M)
    (hlarge : 2 + frontierGradientBound ≤ M) {n : ℕ} (z : Space n) (k : Fin (n + 1))
    (hfirst : ∀ j : Fin (n + 1), j < k → 1 ≤ |z j|) (hk : |z k| < 1) :
    gradient (chain M) z k ≤ -1 := by
  rw [chain_gradient]
  change gradient (extensive M) z k + gradient Cutoffs.frontier z k ≤ -1
  by_cases hsmall : |z k| < 1/8
  · rw [frontier_gradient_coordinate_near z k hfirst hsmall]
    have := extensive_gradient_nonpos hM z k
    linarith
  · have ha := extensive_frontier_coordinate hM z k hfirst
    rw [profile_deriv_plateau M (le_of_not_gt hsmall) hk.le] at ha
    have hb := frontier_gradient_coordinate_le z k
    linarith

theorem chain_frontier_norm_lower {M : ℝ} (hM : 0 ≤ M)
    (hlarge : 2 + frontierGradientBound ≤ M) {n : ℕ} (z : Space n) (k : Fin (n + 1))
    (hfirst : ∀ j : Fin (n + 1), j < k → 1 ≤ |z j|) (hk : |z k| < 1) :
    1 ≤ ‖gradient (chain M) z‖ := by
  have h := chain_frontier_nonstationary hM hlarge z k hfirst hk
  have hn : |gradient (chain M) z k| ≤ ‖gradient (chain M) z‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (gradient (chain M) z) k
  have hab := neg_le_abs (gradient (chain M) z k)
  linarith

end Smoothness2601.ExtensiveChain
