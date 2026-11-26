import FreshGradientMinimax.PathIncidence

/-! Coordinate truncation and the two exposed endpoint bands of a finite path. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

def coordinateMask {n : ℕ} (S : Finset (Fin n)) : Euclid n →L[ℝ] Euclid n :=
  coordinateMultiplier (fun i => if i ∈ S then 1 else 0)

@[simp]
theorem coordinateMask_apply {n : ℕ} (S : Finset (Fin n)) (x : Euclid n) (i : Fin n) :
    coordinateMask S x i = if i ∈ S then x i else 0 := by
  simp only [coordinateMask, coordinateMultiplier_apply]
  split_ifs <;> simp

theorem coordinateMask_abs_le {n : ℕ} (S : Finset (Fin n)) (x : Euclid n) (i : Fin n) :
    |coordinateMask S x i| ≤ |x i| := by
  rw [coordinateMask_apply]
  split_ifs
  · exact le_rfl
  · simp

theorem coordinateMask_norm_le {n : ℕ} (S : Finset (Fin n)) (x : Euclid n) :
    ‖coordinateMask S x‖ ≤ ‖x‖ := by
  apply coordinateMultiplier_norm_le
  intro i
  split_ifs <;> norm_num

def pathVisible (n w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => i.val < w ∨ n ≤ i.val + w)

@[simp]
theorem mem_pathVisible {n w : ℕ} (i : Fin n) :
    i ∈ pathVisible n w ↔ i.val < w ∨ n ≤ i.val + w := by
  simp [pathVisible]

theorem pathVisible_mono {n u w : ℕ} (h : u ≤ w) : pathVisible n u ⊆ pathVisible n w := by
  intro i hi
  simp only [mem_pathVisible] at hi ⊢
  omega

theorem pathVisible_first {n w : ℕ} (hw : 0 < w) : (0 : Fin (n + 1)) ∈ pathVisible (n + 1) w := by
  simp only [mem_pathVisible, Fin.val_zero]
  exact Or.inl hw

theorem pathVisible_last {n w : ℕ} (hw : 0 < w) : Fin.last n ∈ pathVisible (n + 1) w := by
  simp only [mem_pathVisible, Fin.val_last]
  omega

theorem pathVisible_expand_edge {n w : ℕ} (i : Fin n)
    (h : i.castSucc ∈ pathVisible (n + 1) w ∨ i.succ ∈ pathVisible (n + 1) w) :
    i.castSucc ∈ pathVisible (n + 1) (w + 1) ∧ i.succ ∈ pathVisible (n + 1) (w + 1) := by
  simp only [mem_pathVisible, Fin.coe_castSucc, Fin.val_succ] at h ⊢
  omega

theorem pathVisible_center_hidden {N t : ℕ} (ht : t ≤ N) :
    (⟨2 * N + 1, by omega⟩ : Fin (4 * N + 4)) ∉ pathVisible (4 * N + 4) (t + 1) ∧
    (⟨2 * N + 2, by omega⟩ : Fin (4 * N + 4)) ∉ pathVisible (4 * N + 4) (t + 1) := by
  simp only [mem_pathVisible]
  omega

end FreshGradientMinimax
