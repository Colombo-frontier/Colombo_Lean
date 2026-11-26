import FreshGradientMinimax.AcceleratedStages
import FreshGradientMinimax.ClipVector

/-! Continuous linear coordinate masks for the exact reveal order. The
masks are defined at every stage, including beyond the end of the chain. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
variable {m : ℕ}

def stageMask (stage : Fin m → ℕ) (t : ℕ) : Euclid m →L[ℝ] Euclid m :=
  coordinateMultiplier (fun j => if stage j ≤ t then 1 else 0)

@[simp]
theorem stageMask_apply (stage : Fin m → ℕ) (t : ℕ) (u : Euclid m) (j : Fin m) :
    stageMask stage t u j = if stage j ≤ t then u j else 0 := by
  simp only [stageMask, coordinateMultiplier_apply]
  split_ifs <;> simp only [one_mul, zero_mul]

theorem stageMask_known (stage : Fin m → ℕ) (t : ℕ) (u : Euclid m) (j : Fin m) (hj : stage j ≤ t) :
    stageMask stage t u j = u j := by rw [stageMask_apply, if_pos hj]

theorem stageMask_hidden (stage : Fin m → ℕ) (t : ℕ) (u : Euclid m) (j : Fin m) (hj : t < stage j) :
    stageMask stage t u j = 0 := by rw [stageMask_apply, if_neg (not_le_of_gt hj)]

theorem stageMask_abs_le (stage : Fin m → ℕ) (t : ℕ) (u : Euclid m) (j : Fin m) :
    |stageMask stage t u j| ≤ |u j| := by
  rw [stageMask_apply]
  split_ifs
  · exact le_refl _
  · simpa only [abs_zero] using abs_nonneg (u j)

theorem stageMask_norm (stage : Fin m → ℕ) (t : ℕ) (u : Euclid m) : ‖stageMask stage t u‖ ≤ ‖u‖ := by
  apply coordinateMultiplier_norm_le
  intro j
  split_ifs <;> norm_num

theorem stageMask_nested (stage : Fin m → ℕ) {t T : ℕ} (h : t ≤ T) (u : Euclid m) :
    stageMask stage t (stageMask stage T u) = stageMask stage t u := by
  ext j
  simp only [stageMask_apply]
  by_cases hj : stage j ≤ t
  · simp only [if_pos hj, if_pos (hj.trans h)]
  · simp only [if_neg hj]

theorem stageMask_congr (stage : Fin m → ℕ) (t : ℕ) (u v : Euclid m)
    (h : ∀ j, stage j ≤ t → u j = v j) : stageMask stage t u = stageMask stage t v := by
  ext j
  simp only [stageMask_apply]
  by_cases hj : stage j ≤ t
  · rw [if_pos hj, if_pos hj, h j hj]
  · rw [if_neg hj, if_neg hj]

theorem stageMask_clip (stage : Fin m → ℕ) (t : ℕ) {R : ℝ} (hR : 0 < R) (u : Euclid m) :
    clipVector R (stageMask stage t u) = stageMask stage t (clipVector R u) := by
  have hz : smoothClip R 0 = 0 := smoothClip_identity hR (by simpa only [abs_zero] using hR.le)
  ext j
  simp only [stageMask_apply, clipVector_apply]
  by_cases hj : stage j ≤ t
  · simp only [if_pos hj]
  · simp only [if_neg hj, hz]

theorem stageMask_comp_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (stage : Fin m → ℕ) (t : ℕ) (A B : E →L[ℝ] Euclid m)
    (h : ∀ j, stage j ≤ t → ∀ x, A x j = B x j) :
    (stageMask stage t).comp A = (stageMask stage t).comp B := by
  apply ContinuousLinearMap.ext
  intro x
  exact stageMask_congr stage t (A x) (B x) (fun j hj => h j hj x)

def acceleratedPrimalPrefix (n k t : ℕ) : Euclid (k * 2 + 1) →L[ℝ] Euclid (k * 2 + 1) :=
  stageMask (acceleratedPrimalStage n) t

def acceleratedDualPrefix (n k t : ℕ) : Euclid (k * (n + 2)) →L[ℝ] Euclid (k * (n + 2)) :=
  stageMask (acceleratedDualStage n) t

theorem acceleratedPrimalPrefix_seed (n k t : ℕ) (u : Euclid (k * 2 + 1)) :
    acceleratedPrimalPrefix n k t u 0 = u 0 := by
  apply stageMask_known
  rw [acceleratedPrimalStage_zero]
  omega

theorem acceleratedPrimalPrefix_clip (n k t : ℕ) (u : Euclid (k * 2 + 1)) :
    clipVector 2 (acceleratedPrimalPrefix n k t u) = acceleratedPrimalPrefix n k t (clipVector 2 u) :=
  stageMask_clip _ _ (by norm_num) _

end FreshGradientMinimax
