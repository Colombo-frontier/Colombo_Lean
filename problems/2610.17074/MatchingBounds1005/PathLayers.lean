import MatchingBounds1005.PathGreen

/-! # The manuscript's deterministic path-layer calendar -/

noncomputable section
open scoped BigOperators InnerProductSpace Matrix

namespace MatchingBounds1005.PathLayers
open BlockGeometry PathGreen

/-- Zero-based block and vertex indices, with the source's one-based layer. -/
def layer (jstar s j : ℕ) : ℕ := s * jstar + min (j + 1) jstar

theorem layer_suffix {jstar s j : ℕ} (hj : jstar ≤ j + 1) :
    layer jstar s j = (s + 1) * jstar := by
  simp only [layer, min_eq_right hj]
  ring

theorem layer_entry {jstar s : ℕ} (hj : 0 < jstar) :
    layer jstar s 0 = s * jstar + 1 := by simp [layer, Nat.min_eq_left hj]

theorem layer_adjacent {jstar s i j : ℕ} (hij : i ≤ j + 1) :
    layer jstar s i ≤ layer jstar s j + 1 := by
  unfold layer
  omega

def layerSpace (M n jstar t : ℕ) : Submodule ℝ
    (BlockSpace (E := EuclideanSpace ℝ (Fin (M + 1))) n) where
  carrier := {z | ∀ s j, t < layer jstar s.val j.val → z s j = 0}
  zero_mem' := by intro s j hj; rfl
  add_mem' hx hy := by intro s j hj; simp [PiLp.add_apply, hx s j hj, hy s j hj]
  smul_mem' c z hz := by intro s j hj; simp [PiLp.smul_apply, hz s j hj]

theorem layerSpace_mono (M n jstar : ℕ) : Monotone (layerSpace M n jstar) := by
  intro t u htu z hz s j hj
  exact hz s j (lt_of_le_of_lt htu hj)

def blockVector (M n : ℕ) (s : Fin (n + 1)) (a : EuclideanSpace ℝ (Fin (M + 1))) :
    BlockSpace (E := EuclideanSpace ℝ (Fin (M + 1))) n :=
  (WithLp.equiv 2 _).symm (Pi.single s a)

theorem blockVector_mem_calendar (M n jstar t : ℕ) (s : Fin (n + 1))
    (a : EuclideanSpace ℝ (Fin (M + 1)))
    (ha : ∀ j, j.val + 1 < jstar → a j = 0)
    (ht : (s.val + 1) * jstar ≤ t) :
    blockVector M n s a ∈ layerSpace M n jstar t := by
  intro r j hj
  by_cases hrs : r = s
  · subst r
    have hsmall : j.val + 1 < jstar := by
      by_contra hn
      have he := layer_suffix (s := s.val) (Nat.le_of_not_gt hn)
      omega
    simpa [blockVector] using ha j hsmall
  · simp [blockVector, Pi.single_eq_of_ne hrs]

theorem blockVector_orthogonal_calendar (M n jstar t : ℕ) (s : Fin (n + 1))
    (a : EuclideanSpace ℝ (Fin (M + 1)))
    (ha : ∀ j, j.val + 1 < jstar → a j = 0)
    (ht : t < (s.val + 1) * jstar) :
    blockVector M n s a ∈ (layerSpace M n jstar t)ᗮ := by
  apply (Submodule.mem_orthogonal _ _).mpr
  intro z hz
  change (∑ r, ⟪z r, (Pi.single s a : Fin (n + 1) → EuclideanSpace ℝ (Fin (M + 1))) r⟫_ℝ) = 0
  rw [Finset.sum_eq_single s]
  · simp only [Pi.single_eq_same]
    change (∑ j, a j * z s j) = 0
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : j.val + 1 < jstar
    · rw [ha j hj, zero_mul]
    · rw [hz s j (by rw [layer_suffix (Nat.le_of_not_gt hj)]; exact ht), mul_zero]
  · intro r _ hrs
    simp [Pi.single_eq_of_ne hrs]
  · simp

theorem suffixVector_supported (A : ℝ) (M : ℕ) (j : Fin (M + 1))
    (hj : j.val + 1 < (M + 2) / 2) : suffixVector A M j = 0 := by
  have hn : j ∉ suffixSet M := by
    simp only [suffixSet, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  simp [suffixVector, suffixFunction, hn]

theorem suffix_readout_mem (A : ℝ) (M n t : ℕ) (s : Fin (n + 1))
    (ht : (s.val + 1) * ((M + 2) / 2) ≤ t) :
    blockVector M n s (suffixVector A M) ∈ layerSpace M n ((M + 2) / 2) t :=
  blockVector_mem_calendar M n _ t s _ (suffixVector_supported A M) ht

theorem suffix_readout_hidden (A : ℝ) (M n t : ℕ) (s : Fin (n + 1))
    (ht : t < (s.val + 1) * ((M + 2) / 2)) :
    blockVector M n s (suffixVector A M) ∈ (layerSpace M n ((M + 2) / 2) t)ᗮ :=
  blockVector_orthogonal_calendar M n _ t s _ (suffixVector_supported A M) ht

theorem pathMatrix_far_zero (L h : ℝ) (M : ℕ) (i j : Fin (M + 1))
    (hij : i.val + 1 < j.val ∨ j.val + 1 < i.val) : pathMatrix L h M i j = 0 := by
  have hne : i ≠ j := by intro he; subst j; omega
  have hlap : laplacian M i j = 0 := by
    unfold laplacian
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro e _
    change incidence M e i * incidence M e j = 0
    by_cases hi : i = e.succ
    · have hj1 : j ≠ e.succ := by intro he; rw [hi, he] at hij; simp at hij
      have hj2 : j ≠ e.castSucc := by
        intro he
        rw [hi, he] at hij
        change (e.val + 1) + 1 < e.val ∨ e.val + 1 < e.val + 1 at hij
        omega
      simp [incidence, hj1, hj2]
    · by_cases hi2 : i = e.castSucc
      · have hj1 : j ≠ e.succ := by
          intro he
          rw [hi2, he] at hij
          change e.val + 1 < e.val + 1 ∨ (e.val + 1) + 1 < e.val at hij
          omega
        have hj2 : j ≠ e.castSucc := by intro he; rw [hi2, he] at hij; simp at hij
        simp [incidence, hj1, hj2]
      · simp [incidence, hi, hi2]
  simp [pathMatrix, shiftedPath, Matrix.diagonal_apply, hne, hlap]

end MatchingBounds1005.PathLayers
