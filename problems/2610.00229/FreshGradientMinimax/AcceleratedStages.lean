import FreshGradientMinimax.EuclidDropFirst

/-! The exact vertex order of E.4: x, the entire dual subchain, z, the
next x. Every informative edge joins consecutive reveal stages. -/

set_option autoImplicit false
namespace FreshGradientMinimax

def acceleratedStageCount (n k : ℕ) : ℕ := k * (n + 4)

def acceleratedPrimalStage (n : ℕ) {k : ℕ} (j : Fin (k * 2 + 1)) : ℕ :=
  (j.val / 2) * (n + 4) + if j.val % 2 = 0 then 0 else n + 3

def acceleratedDualStage (n : ℕ) {k : ℕ} (j : Fin (k * (n + 2))) : ℕ :=
  (finProdFinEquiv.symm j).1.val * (n + 4) + (finProdFinEquiv.symm j).2.val + 1

theorem acceleratedPrimalStage_x (n : ℕ) {k : ℕ} (i : Fin k) :
    acceleratedPrimalStage n (interleavedX i) = i.val * (n + 4) := by
  unfold acceleratedPrimalStage
  have hv : (interleavedX i).val = 2 * i.val := by simp [interleavedX, finProdFinEquiv]
  rw [hv]
  simp

theorem acceleratedPrimalStage_z (n : ℕ) {k : ℕ} (i : Fin k) :
    acceleratedPrimalStage n (interleavedZ i) = i.val * (n + 4) + n + 3 := by
  unfold acceleratedPrimalStage
  have hv : (interleavedZ i).val = 1 + 2 * i.val := rfl
  rw [hv]
  have hd : (1 + 2 * i.val) / 2 = i.val := by omega
  have hm : (1 + 2 * i.val) % 2 = 1 := by omega
  simp only [hd, hm, Nat.one_ne_zero, if_false]
  omega

theorem acceleratedPrimalStage_nextX (n : ℕ) {k : ℕ} (i : Fin k) :
    acceleratedPrimalStage n (interleavedNextX i) = (i.val + 1) * (n + 4) := by
  unfold acceleratedPrimalStage
  have hv : (interleavedNextX i).val = 1 + 2 * i.val + 1 := rfl
  rw [hv]
  have hd : (1 + 2 * i.val + 1) / 2 = i.val + 1 := by omega
  have hm : (1 + 2 * i.val + 1) % 2 = 0 := by omega
  simp only [hd, hm, if_true, add_zero]

theorem acceleratedPrimalStage_zero (n k : ℕ) : acceleratedPrimalStage n (0 : Fin (k * 2 + 1)) = 0 := by
  simp [acceleratedPrimalStage]

theorem acceleratedPrimalStage_last (n k : ℕ) :
    acceleratedPrimalStage n (Fin.last (k * 2)) = acceleratedStageCount n k := by
  simp [acceleratedPrimalStage, acceleratedStageCount]

theorem acceleratedDualStage_block (n : ℕ) {k : ℕ} (i : Fin k) (a : Fin (n + 2)) :
    acceleratedDualStage n (finProdFinEquiv (i, a)) = i.val * (n + 4) + a.val + 1 := by
  simp only [acceleratedDualStage, Equiv.symm_apply_apply]

theorem acceleratedStages_first_edge (n : ℕ) {k : ℕ} (i : Fin k) :
    acceleratedDualStage n (finProdFinEquiv (i, (0 : Fin (n + 2)))) =
      acceleratedPrimalStage n (interleavedX i) + 1 := by
  rw [acceleratedDualStage_block, acceleratedPrimalStage_x]
  rfl

theorem acceleratedStages_internal_edge (n : ℕ) {k : ℕ} (i : Fin k) (a : Fin (n + 1)) :
    acceleratedDualStage n (finProdFinEquiv (i, a.succ)) =
      acceleratedDualStage n (finProdFinEquiv (i, a.castSucc)) + 1 := by
  rw [acceleratedDualStage_block, acceleratedDualStage_block]
  simp only [Fin.val_succ, Fin.coe_castSucc]
  omega

theorem acceleratedStages_last_edge (n : ℕ) {k : ℕ} (i : Fin k) :
    acceleratedDualStage n (finProdFinEquiv (i, Fin.last (n + 1))) + 1 =
      acceleratedPrimalStage n (interleavedZ i) := by
  rw [acceleratedDualStage_block, acceleratedPrimalStage_z]
  simp only [Fin.val_last]
  omega

theorem acceleratedStages_nonlinear_edge (n : ℕ) {k : ℕ} (i : Fin k) :
    acceleratedPrimalStage n (interleavedNextX i) = acceleratedPrimalStage n (interleavedZ i) + 1 := by
  rw [acceleratedPrimalStage_nextX, acceleratedPrimalStage_z]
  ring

theorem acceleratedStages_vertex_count (n k : ℕ) :
    (k * 2 + 1) + k * (n + 2) = acceleratedStageCount n k + 1 := by
  unfold acceleratedStageCount
  ring

theorem acceleratedStages_last_z (n : ℕ) {k : ℕ} (hk : 0 < k) :
    acceleratedPrimalStage n (interleavedZ (⟨k - 1, by omega⟩ : Fin k)) + 1 = acceleratedStageCount n k := by
  rw [acceleratedPrimalStage_z]
  unfold acceleratedStageCount
  have he : k - 1 + 1 = k := by omega
  nlinarith only [he]

theorem acceleratedStages_terminal_hidden (n : ℕ) {k H : ℕ} (hk : 0 < k)
    (hH : 2 * H + 2 ≤ acceleratedStageCount n k) :
    H < acceleratedPrimalStage n (interleavedZ (⟨k - 1, by omega⟩ : Fin k)) := by
  have h := acceleratedStages_last_z n hk
  omega

end FreshGradientMinimax
