import RandomizedFO2003.EpochRestartDecrease
import Mathlib.Algebra.Order.Floor.Ring

namespace RandomizedFO2003.Accelerated

noncomputable section

def rawMomentum (η ρ B : ℝ) : ℝ := 4 * Real.sqrt (ρ * B * η)
def epochHorizon (η ρ B : ℝ) : ℕ := ⌊1 / rawMomentum η ρ B⌋₊
def roundedMomentum (η ρ B : ℝ) : ℝ := 1 / (epochHorizon η ρ B : ℝ)
def accuracyRadius (ε ρ : ℝ) : ℝ := Real.sqrt ((ε / 512) / ρ)
def stepSize (L : ℝ) : ℝ := 1 / (4 * L)

/-- Rounding the reciprocal down produces a positive integer horizon and
changes momentum by at most a factor of two. -/
theorem rounded_reciprocal_bounds {t : ℝ} (ht : 0 < t) (htsmall : t ≤ 1 / 2) :
    0 < ⌊1 / t⌋₊ ∧ t ≤ 1 / (⌊1 / t⌋₊ : ℝ) ∧
      1 / (⌊1 / t⌋₊ : ℝ) ≤ 2 * t ∧ 1 / (⌊1 / t⌋₊ : ℝ) ≤ 1 := by
  have htwo : (2 : ℝ) ≤ 1 / t := by rw [le_div_iff₀ ht]; linarith
  have hN : 0 < ⌊1 / t⌋₊ := Nat.floor_pos.mpr (by linarith)
  have hNpos : (0 : ℝ) < (⌊1 / t⌋₊ : ℝ) := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ (⌊1 / t⌋₊ : ℝ) := by exact_mod_cast hN
  have hlo := (le_div_iff₀ ht).mp (Nat.floor_le (show 0 ≤ 1 / t by positivity))
  have hhi := (div_lt_iff₀ ht).mp (Nat.lt_floor_add_one (1 / t))
  refine ⟨hN, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ hNpos]
    nlinarith
  · rw [div_le_iff₀ hNpos]
    nlinarith
  · rw [div_le_iff₀ hNpos]
    simpa using hN1

theorem rawMomentum_sq {η ρ B : ℝ} (hη : 0 ≤ η) (hρ : 0 ≤ ρ) (hB : 0 ≤ B) :
    rawMomentum η ρ B ^ 2 = 16 * ρ * B * η := by
  have hs := Real.sq_sqrt (show 0 ≤ ρ * B * η by positivity)
  unfold rawMomentum
  nlinarith

theorem rawMomentum_pos {η ρ B : ℝ} (hη : 0 < η) (hρ : 0 < ρ) (hB : 0 < B) :
    0 < rawMomentum η ρ B := by unfold rawMomentum; positivity

theorem roundedMomentum_conditions {η ρ B : ℝ} (hη : 0 < η) (hρ : 0 < ρ) (hB : 0 < B)
    (hsmall : rawMomentum η ρ B ≤ 1 / 2) :
    0 < epochHorizon η ρ B ∧ 0 < roundedMomentum η ρ B ∧
      roundedMomentum η ρ B ≤ 1 ∧
      roundedMomentum η ρ B * (epochHorizon η ρ B : ℝ) = 1 ∧
      16 * ρ * B * η ≤ roundedMomentum η ρ B ^ 2 ∧
      roundedMomentum η ρ B ^ 2 ≤ 64 * ρ * B * η := by
  have ht := rawMomentum_pos hη hρ hB
  have hs := rounded_reciprocal_bounds ht hsmall
  change 0 < epochHorizon η ρ B ∧ rawMomentum η ρ B ≤ roundedMomentum η ρ B ∧
    roundedMomentum η ρ B ≤ 2 * rawMomentum η ρ B ∧ roundedMomentum η ρ B ≤ 1 at hs
  have hθ : 0 < roundedMomentum η ρ B := ht.trans_le hs.2.1
  have hN : (epochHorizon η ρ B : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hs.1
  have hl := (sq_le_sq₀ ht.le hθ.le).mpr hs.2.1
  have hu := (sq_le_sq₀ hθ.le (by positivity : 0 ≤ 2 * rawMomentum η ρ B)).mpr hs.2.2.1
  have he := rawMomentum_sq hη.le hρ.le hB.le
  refine ⟨hs.1, hθ, hs.2.2.2, ?_, ?_, ?_⟩
  · simp [roundedMomentum, hN]
  · linarith
  · nlinarith

theorem rounded_terminal_bound {η ρ B : ℝ} (hη : 0 < η) (hρ : 0 < ρ) (hB : 0 < B)
    (hsmall : rawMomentum η ρ B ≤ 1 / 2) :
    4 * B / (η * (epochHorizon η ρ B : ℝ) ^ 2) +
      2 * roundedMomentum η ρ B * B / (η * (epochHorizon η ρ B : ℝ)) + 4 * ρ * B ^ 2 ≤
        388 * ρ * B ^ 2 := by
  have hs := roundedMomentum_conditions hη hρ hB hsmall
  have hn : (epochHorizon η ρ B : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hs.1
  have he : 4 * B / (η * (epochHorizon η ρ B : ℝ) ^ 2) +
      2 * roundedMomentum η ρ B * B / (η * (epochHorizon η ρ B : ℝ)) =
      (6 * B / η) * roundedMomentum η ρ B ^ 2 := by
    unfold roundedMomentum
    field_simp
    ring
  rw [he]
  have hm := mul_le_mul_of_nonneg_left hs.2.2.2.2.2 (show 0 ≤ 6 * B / η by positivity)
  have hc : (6 * B / η) * (64 * ρ * B * η) = 384 * ρ * B ^ 2 := by field_simp; ring
  rw [hc] at hm
  linarith

theorem accuracyRadius_pos {ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ) :
    0 < accuracyRadius ε ρ := by unfold accuracyRadius; positivity

theorem accuracyRadius_sq {ε ρ : ℝ} (hε : 0 ≤ ε) (hρ : 0 < ρ) :
    ρ * accuracyRadius ε ρ ^ 2 = ε / 512 := by
  unfold accuracyRadius
  rw [Real.sq_sqrt (by positivity)]
  field_simp
  ring

theorem stepSize_pos {L : ℝ} (hL : 0 < L) : 0 < stepSize L := by
  unfold stepSize
  positivity

theorem stepSize_mul {L : ℝ} (hL : 0 < L) : L * stepSize L = 1 / 4 := by
  unfold stepSize
  field_simp
  ring

/-- The supplied high-accuracy regime ensures the raw momentum is small
enough to round its reciprocal without losing more than a factor of two. -/
theorem accuracy_rawMomentum_small {ε L ρ : ℝ} (hε : 0 < ε) (hL : 0 < L) (hρ : 0 < ρ)
    (haccuracy : ε ≤ L ^ 2 / ρ) :
    rawMomentum (stepSize L) ρ (accuracyRadius ε ρ) ≤ 1 / 2 := by
  have hB := accuracyRadius_pos hε hρ
  have hs := accuracyRadius_sq hε.le hρ
  have hr := (le_div_iff₀ hρ).mp haccuracy
  have hsρ := congrArg (fun z : ℝ => ρ * z) hs
  have hsq : (16 * ρ * accuracyRadius ε ρ) ^ 2 ≤ L ^ 2 := by nlinarith [sq_nonneg L]
  have hb : 16 * ρ * accuracyRadius ε ρ ≤ L :=
    (sq_le_sq₀ (by positivity) hL.le).mp hsq
  have hm := rawMomentum_sq (stepSize_pos hL).le hρ.le hB.le
  have hbound : 16 * ρ * accuracyRadius ε ρ * stepSize L ≤ 1 / 4 := by
    calc
      _ ≤ L * stepSize L := mul_le_mul_of_nonneg_right hb (stepSize_pos hL).le
      _ = 1 / 4 := stepSize_mul hL
  nlinarith [rawMomentum_pos (stepSize_pos hL) hρ hB]

end

end RandomizedFO2003.Accelerated
