import NCBall.UpperBatch

/-! # Explicit positive integer budgets in the nontrivial radius regime

The large-radius case uses the separate `LocalGoldsteinGap` certificate.
Here ν ε ≤ Δ and ε ≤ V give a direct ceiling-based parameter choice with
the desired V² Δ / (ν ε³) scale and a trajectory of length at most 5 Δ / ε.
-/

noncomputable section
namespace NCBall

def upperBlockLength (V ε : ℝ) : ℕ := ⌈144 * V ^ 2 / ε ^ 2⌉₊
def upperBlockCount (Δ ν ε : ℝ) : ℕ := ⌈4 * Δ / (ν * ε)⌉₊
def upperClipRadius (V ν ε : ℝ) : ℝ := ν / (upperBlockLength V ε : ℝ)
def upperLearningRate (V ν ε : ℝ) : ℝ := upperClipRadius V ν ε * ε / (6 * V ^ 2)

theorem upperBlockLength_pos {V ε : ℝ} (hε : 0 < ε) (hV : ε ≤ V) : 0 < upperBlockLength V ε := by
  have hv : 0 < V := hε.trans_le hV
  apply Nat.ceil_pos.mpr
  positivity

theorem upperBlockCount_pos {Δ ν ε : ℝ} (hν : 0 < ν) (hε : 0 < ε) (hΔ : ν * ε ≤ Δ) :
    0 < upperBlockCount Δ ν ε := by
  have hd : 0 < Δ := lt_of_lt_of_le (mul_pos hν hε) hΔ
  apply Nat.ceil_pos.mpr
  positivity

theorem upperClipRadius_pos {V ν ε : ℝ} (hν : 0 < ν) (hε : 0 < ε) (hV : ε ≤ V) :
    0 < upperClipRadius V ν ε := div_pos hν (Nat.cast_pos.mpr (upperBlockLength_pos hε hV))

theorem upperLearningRate_pos {V ν ε : ℝ} (hν : 0 < ν) (hε : 0 < ε) (hV : ε ≤ V) :
    0 < upperLearningRate V ν ε := by
  have hv : 0 < V := hε.trans_le hV
  exact div_pos (mul_pos (upperClipRadius_pos hν hε hV) hε) (by positivity)

theorem upper_block_radius_eq {V ν ε : ℝ} (hε : 0 < ε) (hV : ε ≤ V) :
    (upperBlockLength V ε : ℝ) * upperClipRadius V ν ε = ν := by
  unfold upperClipRadius
  have hm : (upperBlockLength V ε : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr (upperBlockLength_pos hε hV))
  field_simp

theorem upperBlockLength_bound {V ε : ℝ} (hε : 0 < ε) (hV : ε ≤ V) :
    (upperBlockLength V ε : ℝ) ≤ 145 * V ^ 2 / ε ^ 2 := by
  have hv : 0 < V := hε.trans_le hV
  have hratio : 1 ≤ V ^ 2 / ε ^ 2 := (le_div_iff₀ (sq_pos_of_pos hε)).2 (by nlinarith)
  have hc := Nat.ceil_lt_add_one (show 0 ≤ 144 * V ^ 2 / ε ^ 2 by positivity)
  dsimp only [upperBlockLength]
  ring_nf at hratio hc ⊢
  linarith

theorem upperBlockCount_bound {Δ ν ε : ℝ} (hν : 0 < ν) (hε : 0 < ε) (hΔ : ν * ε ≤ Δ) :
    (upperBlockCount Δ ν ε : ℝ) ≤ 5 * Δ / (ν * ε) := by
  have hd : 0 < Δ := lt_of_lt_of_le (mul_pos hν hε) hΔ
  have hratio : 1 ≤ Δ / (ν * ε) := (le_div_iff₀ (mul_pos hν hε)).2 (by simpa using hΔ)
  have hc := Nat.ceil_lt_add_one (show 0 ≤ 4 * Δ / (ν * ε) by positivity)
  dsimp only [upperBlockCount]
  ring_nf at hratio hc ⊢
  linarith

theorem upper_total_steps_bound {V Δ ν ε : ℝ} (hν : 0 < ν) (hε : 0 < ε)
    (hV : ε ≤ V) (hΔ : ν * ε ≤ Δ) :
    (upperBlockCount Δ ν ε * upperBlockLength V ε : ℕ) ≤ 725 * V ^ 2 * Δ / (ν * ε ^ 3) := by
  have hd : 0 < Δ := lt_of_lt_of_le (mul_pos hν hε) hΔ
  push_cast
  calc
    _ ≤ (5 * Δ / (ν * ε)) * (145 * V ^ 2 / ε ^ 2) :=
      mul_le_mul (upperBlockCount_bound hν hε hΔ) (upperBlockLength_bound hε hV)
        (Nat.cast_nonneg _) (by positivity)
    _ = _ := by ring

theorem upper_total_path_bound {V Δ ν ε : ℝ} (hν : 0 < ν) (hε : 0 < ε)
    (hV : ε ≤ V) (hΔ : ν * ε ≤ Δ) :
    (upperBlockCount Δ ν ε * upperBlockLength V ε : ℕ) * upperClipRadius V ν ε ≤ 5 * Δ / ε := by
  push_cast
  rw [mul_assoc, upper_block_radius_eq hε hV]
  calc
    _ ≤ (5 * Δ / (ν * ε)) * ν := mul_le_mul_of_nonneg_right (upperBlockCount_bound hν hε hΔ) hν.le
    _ = _ := by field_simp; ring

theorem upper_parameter_accuracy {V Δ ν ε : ℝ} (hν : 0 < ν) (hε : 0 < ε)
    (hV : ε ≤ V) (hΔ : ν * ε ≤ Δ) :
    let m : ℝ := upperBlockLength V ε
    let K : ℝ := upperBlockCount Δ ν ε
    let D := upperClipRadius V ν ε
    let α := upperLearningRate V ν ε
    Δ / (D * m * K) + 2 * D / (α * m) + α * V ^ 2 / (2 * D) + Real.sqrt m * |V| / m ≤ ε / 2 := by
  let m : ℝ := upperBlockLength V ε
  let K : ℝ := upperBlockCount Δ ν ε
  let D := upperClipRadius V ν ε
  let α := upperLearningRate V ν ε
  change Δ / (D * m * K) + 2 * D / (α * m) + α * V ^ 2 / (2 * D) + Real.sqrt m * |V| / m ≤ ε / 2
  have hm : 0 < m := Nat.cast_pos.mpr (upperBlockLength_pos hε hV)
  have hK : 0 < K := Nat.cast_pos.mpr (upperBlockCount_pos hν hε hΔ)
  have hD : 0 < D := upperClipRadius_pos hν hε hV
  have hv : 0 < V := hε.trans_le hV
  have hmm : 144 * V ^ 2 ≤ ε ^ 2 * m := by
    have hc := Nat.le_ceil (144 * V ^ 2 / ε ^ 2)
    exact (div_le_iff₀ (sq_pos_of_pos hε)).mp hc |>.trans_eq (mul_comm _ _)
  have hKK : 4 * Δ ≤ ν * ε * K := by
    have hc := Nat.le_ceil (4 * Δ / (ν * ε))
    exact (div_le_iff₀ (mul_pos hν hε)).mp hc |>.trans_eq (mul_comm _ _)
  have hDm : D * m = ν := by simpa only [mul_comm] using upper_block_radius_eq (ν := ν) hε hV
  have ht₁ : Δ / (D * m * K) ≤ ε / 4 := by
    rw [hDm]
    apply (div_le_iff₀ (mul_pos hν hK)).2
    nlinarith
  have ht₂ : 2 * D / (α * m) ≤ ε / 12 := by
    have he : 2 * D / (α * m) = 12 * V ^ 2 / (ε * m) := by
      dsimp only [α, upperLearningRate]
      change 2 * D / (D * ε / (6 * V ^ 2) * m) = _
      field_simp
      ring
    rw [he]
    apply (div_le_iff₀ (mul_pos hε hm)).2
    nlinarith
  have ht₃ : α * V ^ 2 / (2 * D) = ε / 12 := by
    dsimp only [α, upperLearningRate]
    change (D * ε / (6 * V ^ 2)) * V ^ 2 / (2 * D) = _
    field_simp
    ring
  have hsq := Real.sq_sqrt hm.le
  have hs := Real.sqrt_nonneg m
  have hsmall : 12 * V ≤ ε * Real.sqrt m := by
    have he : (ε * Real.sqrt m) ^ 2 = ε ^ 2 * m := by rw [mul_pow, hsq]
    nlinarith [mul_nonneg hε.le hs]
  have ht₄ : Real.sqrt m * |V| / m ≤ ε / 12 := by
    rw [abs_of_pos hv]
    apply (div_le_iff₀ hm).2
    have hp := mul_le_mul_of_nonneg_right hsmall hs
    nlinarith
  linarith

end NCBall
