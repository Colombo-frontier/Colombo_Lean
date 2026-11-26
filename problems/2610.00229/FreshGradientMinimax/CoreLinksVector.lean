import FreshGradientMinimax.EuclidBlocks
import FreshGradientMinimax.RootLinkLipschitz
import FreshGradientMinimax.CoreLemma

/-! The vector of all original square links and its dimension-free Jacobian bound. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators

def coreLinks {n : ℕ} (u : Euclid (n + 1)) : Euclid (n + n) :=
  euclidAppend (adjacentVector (rootLink (-1)) u) (adjacentVector (rootLink 1) u)

@[simp]
theorem coreLinks_plus {n : ℕ} (u : Euclid (n + 1)) (e : Fin n) :
    coreLinks u (e.castAdd n) = coreLinkPlus (u e.castSucc) (u e.succ) := by
  simp only [coreLinks, euclidAppend_left, adjacentVector_apply, coreLinkPlus_rootLink]

@[simp]
theorem coreLinks_minus {n : ℕ} (u : Euclid (n + 1)) (e : Fin n) :
    coreLinks u (e.natAdd n) = coreLinkMinus (u e.castSucc) (u e.succ) := by
  simp only [coreLinks, euclidAppend_right, adjacentVector_apply, coreLinkMinus_rootLink]

theorem coreLinks_nonneg {n : ℕ} (u : Euclid (n + 1)) (i : Fin (n + n)) : 0 ≤ coreLinks u i := by
  refine Fin.addCases (fun e => ?_) (fun e => ?_) i
  · rw [coreLinks_plus]; exact Real.sqrt_nonneg _
  · rw [coreLinks_minus]; exact Real.sqrt_nonneg _

theorem coreLinks_coordinate_bound {n : ℕ} (u : Euclid (n + 1)) (i : Fin (n + n)) :
    |coreLinks u i| ≤ 4 := by
  refine Fin.addCases (fun e => ?_) (fun e => ?_) i
  · rw [coreLinks_plus]; exact coreLinkPlus_bound _ _
  · rw [coreLinks_minus]; exact coreLinkMinus_bound _ _

theorem coreLinks_norm_sq {n : ℕ} (u : Euclid (n + 1)) :
    ‖coreLinks u‖ ^ 2 = ∑ e : Fin n,
      (coreLinkPlus (u e.castSucc) (u e.succ) ^ 2 + coreLinkMinus (u e.castSucc) (u e.succ) ^ 2) := by
  rw [euclid_norm_sq, Fin.sum_univ_add, Finset.sum_add_distrib]
  simp only [coreLinks_plus, coreLinks_minus]

theorem coreChain_seed_links_identity {n : ℕ} (u : Euclid (n + 1)) :
    coreChain u = coreSeed u + ‖coreLinks u‖ ^ 2 := by
  rw [coreLinks_norm_sq]
  exact squareLinkCore_identity (fun i => u i)

theorem coreLinks_norm_sq_bound {n : ℕ} (u : Euclid (n + 1)) :
    ‖coreLinks u‖ ^ 2 ≤ 32 * (n : ℝ) := by
  rw [euclid_norm_sq]
  calc
    _ ≤ ∑ _i : Fin (n + n), (4 : ℝ) ^ 2 := Finset.sum_le_sum (fun i _ => by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (coreLinks_coordinate_bound u i) 2)
    _ = _ := by simp; ring

theorem coreLinks_contDiff {n : ℕ} {m : ℕ∞} : ContDiff ℝ m (@coreLinks n) := by
  apply (contDiff_piLp 2).mpr
  intro i
  refine Fin.addCases (fun e => ?_) (fun e => ?_) i
  · simp_rw [coreLinks_plus, coreLinkPlus_rootLink]
    exact (rootLink_contDiff (-1)).comp
      ((EuclideanSpace.proj (𝕜 := ℝ) e.castSucc).contDiff.prodMk
        (EuclideanSpace.proj (𝕜 := ℝ) e.succ).contDiff)
  · simp_rw [coreLinks_minus, coreLinkMinus_rootLink]
    exact (rootLink_contDiff 1).comp
      ((EuclideanSpace.proj (𝕜 := ℝ) e.castSucc).contDiff.prodMk
        (EuclideanSpace.proj (𝕜 := ℝ) e.succ).contDiff)

theorem coreLinks_sub_norm {n : ℕ} (u v : Euclid (n + 1)) :
    ‖coreLinks u - coreLinks v‖ ≤ 57 * ‖u - v‖ := by
  have hm := rootLink_adjacent_sub_norm (by norm_num : |(-1 : ℝ)| = 1) u v
  have hp := rootLink_adjacent_sub_norm (by norm_num : |(1 : ℝ)| = 1) u v
  have hm2 := pow_le_pow_left₀ (norm_nonneg _) hm 2
  have hp2 := pow_le_pow_left₀ (norm_nonneg _) hp 2
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [coreLinks, coreLinks, euclidAppend_sub, euclidAppend_norm_sq]
  nlinarith only [hm2, hp2, sq_nonneg ‖u - v‖]

theorem coreLinks_lipschitz (n : ℕ) : LipschitzWith 57 (@coreLinks n) := by
  apply lipschitzWith_iff_norm_sub_le.mpr
  intro u v
  exact coreLinks_sub_norm u v

theorem coreLinks_fderiv_norm {n : ℕ} (u : Euclid (n + 1)) : ‖fderiv ℝ (@coreLinks n) u‖ ≤ 57 :=
  norm_fderiv_le_of_lipschitz ℝ (coreLinks_lipschitz n)

theorem coreLinks_zero (n : ℕ) : coreLinks (0 : Euclid (n + 1)) = 0 := by
  have h := coreLinks_flat (by norm_num : |(0 : ℝ)| ≤ 1 / 2) 0
  ext i
  refine Fin.addCases (fun e => ?_) (fun e => ?_) i
  · simpa only [coreLinks_plus, PiLp.zero_apply] using h.1
  · simpa only [coreLinks_minus, PiLp.zero_apply] using h.2.1

end FreshGradientMinimax
