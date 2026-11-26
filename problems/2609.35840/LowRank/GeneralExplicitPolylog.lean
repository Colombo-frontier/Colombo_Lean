import LowRank.GeneralMinimaxUpper
import LowRank.CubicExplicitPolylog

/-! An explicit logarithm of the smaller dimension, rank and inverse
accuracy bounds the complete upper rate for every finite p >= 1. -/

namespace LowRank
open scoped ENNReal
noncomputable section
universe u

theorem confidentRitzTolerance_reciprocal_le_scaled {k s d : ℕ} {γ ε W M : ℝ}
    (hk : 0 < k) (hs : 0 < s) (hγ : 0 < γ) (hε : 0 < ε)
    (hW : 1 ≤ W) (hM : 1 ≤ M)
    (hwidth : (s : ℝ) * ε ≤ W * (k : ℝ)) (hgap : ε ≤ M * (k : ℝ) * γ) :
    2 / confidentRitzTolerance γ (40 * (k : ℝ)) s d ≤
      1024 * W * M * (k : ℝ) ^ 2 * ((d : ℝ) + 1) / ε := by
  have hWp : 0 < W := by linarith
  have hMp : 0 < M := by linarith
  have hWM : 0 < W * M := mul_pos hWp hMp
  have he : 0 < ε / (W * M) := div_pos hε hWM
  have hw' : (s : ℝ) * (ε / (W * M)) ≤ 14 * (k : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hM (by positivity : 0 ≤ W * (k : ℝ))
    have hw : (s : ℝ) * ε ≤ (k : ℝ) * (W * M) := by nlinarith
    calc
      _ = ((s : ℝ) * ε) / (W * M) := by ring
      _ ≤ (k : ℝ) := (div_le_iff₀ hWM).mpr hw
      _ ≤ _ := by have hkz : 0 ≤ (k : ℝ) := Nat.cast_nonneg k; linarith
  have hg' : ε / (W * M) ≤ (k : ℝ) * γ := by
    apply (div_le_iff₀ hWM).mpr
    have hw := mul_le_mul_of_nonneg_left hW (by positivity : 0 ≤ M * (k : ℝ) * γ)
    nlinarith
  have h := confidentRitzTolerance_reciprocal_le (d := d) hk hs hγ he hw' hg'
  rw [div_div_eq_mul_div] at h
  convert h using 1 <;> ring

def generalLogArgument (p : ℝ) (N k : ℕ) (ε : ℝ) : ℝ :=
  1024 * (2 * (4 : ℝ) ^ (p / 2) + 6) * max 1 (p / 2) *
    (k : ℝ) ^ 2 * ((N : ℝ) + 1) / ε

def generalPolylog (p : ℝ) (N k : ℕ) (ε : ℝ) : ℝ :=
  8 * (2 * Real.log (generalLogArgument p N k ε) * powerBoostCost p + (powerBoostOrder p : ℝ) + 2) +
    (4 * (4 : ℝ) ^ (p / 2) + 12) *
      (2 * Real.log (generalLogArgument p N k ε) + (powerBoostOrder p : ℝ) + 2) +
        (4 : ℝ) ^ (p / 2) + 3

theorem generalQueryLogFactor_le_polylog {p ε : ℝ} {N k : ℕ}
    (hk : 0 < k) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    generalQueryLogFactor p N k ε ≤ generalPolylog p N k ε := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkR : 0 < (k : ℝ) := by linarith
  have hM := schattenLossFactor_pos p
  have hM1 : 1 ≤ max 1 (p / 2) := le_max_left _ _
  have hfour : 0 ≤ (4 : ℝ) ^ (p / 2) := Real.rpow_nonneg (by norm_num) _
  have hW : 1 ≤ 2 * (4 : ℝ) ^ (p / 2) + 6 := by linarith
  have ha := accuracyScale_ge_one hε hε1
  have has : accuracyScale ε * ε ≤ 1 := by
    rw [mul_comm, ← cubicKrylovGap_eq_mul_scale hε]
    exact cubicKrylovGap_le_one hε.le hε1
  have hwidthN : ((2 * k + 2 : ℕ) : ℝ) * ε ≤ (2 * (4 : ℝ) ^ (p / 2) + 6) * (k : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hε1 (Nat.cast_nonneg (2 * k + 2))
    have hpw := mul_nonneg hfour (Nat.cast_nonneg k)
    push_cast at h ⊢
    nlinarith
  have hwidthW : ((2 * generalWideKrylovRank p k ε + 2 : ℕ) : ℝ) * ε ≤
      (2 * (4 : ℝ) ^ (p / 2) + 6) * (k : ℝ) := by
    calc
      _ ≤ ((2 * (4 : ℝ) ^ (p / 2) + 6) * ((k : ℝ) * accuracyScale ε)) * ε :=
        mul_le_mul_of_nonneg_right (generalWideKrylovBlockWidth_le hk hε hε1) hε.le
      _ = ((2 * (4 : ℝ) ^ (p / 2) + 6) * (k : ℝ)) * (accuracyScale ε * ε) := by ring
      _ ≤ ((2 * (4 : ℝ) ^ (p / 2) + 6) * (k : ℝ)) * 1 :=
        mul_le_mul_of_nonneg_left has (by positivity)
      _ = _ := by ring
  have hgapN : ε ≤ max 1 (p / 2) * (k : ℝ) * weightedNarrowError p ε := by
    have hka := one_le_mul_of_one_le_of_one_le hk1 ha
    have he : max 1 (p / 2) * (k : ℝ) * weightedNarrowError p ε = ε * ((k : ℝ) * accuracyScale ε) := by
      unfold weightedNarrowError
      rw [cubicKrylovGap_eq_mul_scale hε]
      field_simp
      ring
    rw [he]
    exact le_mul_of_one_le_right hε.le hka
  have hgapW : ε ≤ max 1 (p / 2) * (k : ℝ) * weightedWideError p k ε := by
    unfold weightedWideError
    rw [mul_div_cancel₀ _ (mul_pos hM hkR).ne']
  have hN := confidentRitzTolerance_reciprocal_le_scaled (d := N) hk (by omega : 0 < 2 * k + 2)
    (weightedNarrowError_pos hε) hε hW hM1 hwidthN hgapN
  have hWb := confidentRitzTolerance_reciprocal_le_scaled (d := N) hk
    (by omega : 0 < 2 * generalWideKrylovRank p k ε + 2) (weightedWideError_pos hk hε) hε hW hM1 hwidthW hgapW
  change 2 / generalNarrowTolerance p N k ε ≤ generalLogArgument p N k ε at hN
  change 2 / generalWideTolerance p N k ε ≤ generalLogArgument p N k ε at hWb
  have hNp := (generalNarrowTolerance_bounds (p := p) (a := N) hk hε hε1).1
  have hWp := (generalWideTolerance_bounds (p := p) (a := N) hk hε hε1).1
  have hn := Real.log_le_log (by positivity : 0 < 2 / generalNarrowTolerance p N k ε) hN
  have hw := Real.log_le_log (by positivity : 0 < 2 / generalWideTolerance p N k ε) hWb
  have hcost := mul_le_mul_of_nonneg_right hn (powerBoostCost_pos p).le
  have hwide := mul_le_mul_of_nonneg_left hw (by positivity : 0 ≤ 4 * (4 : ℝ) ^ (p / 2) + 12)
  unfold generalQueryLogFactor generalPolylog
  nlinarith

theorem rectangularQueryComplexity_le_general_explicit_polylog {a b k : ℕ}
    (hk0 : 0 < k) (hka : k ≤ a) (hkb : k ≤ b)
    {p ε δ : ℝ} (hp : 1 ≤ p) (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : δ ≤ 19 / 20) :
    rectangularQueryComplexity.{u} a b k p ε δ ≤
      ENNReal.ofReal (generalPolylog p (min a b) k ε * targetRate (min a b) k ε) := by
  apply (rectangularQueryComplexity_le_general_minimum_rate hk0 hka hkb hp hε hε1 hδ).trans
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_right (generalQueryLogFactor_le_polylog hk0 hε hε1)
  exact le_min (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg k) (accuracyScale_pos hε).le)

theorem rectangularQueryComplexity_two_sided_general_explicit_polylog {p : ℝ} (hp : 1 ≤ p) :
    ∃ c : ℝ, 0 < c ∧ ∀ (a b k : ℕ) (ε δ : ℝ),
      0 < k → k < min a b → 0 < ε → ε ≤ 1 → 1 / 5 ≤ δ → δ ≤ 19 / 20 →
      ENNReal.ofReal (c * targetRate (min a b) k ε) ≤ rectangularQueryComplexity.{u} a b k p ε δ ∧
      rectangularQueryComplexity.{u} a b k p ε δ ≤
        ENNReal.ofReal (generalPolylog p (min a b) k ε * targetRate (min a b) k ε) := by
  obtain ⟨c, hc, hlow⟩ := rectangularQueryComplexity_rate.{u} (by linarith : 0 < p)
  refine ⟨c, hc, ?_⟩
  intro a b k ε δ hk hkN hε hε1 hδ hδ1
  exact ⟨hlow a b k ε δ hk hkN hε hε1 hδ,
    rectangularQueryComplexity_le_general_explicit_polylog hk (lt_min_iff.mp hkN).1.le
      (lt_min_iff.mp hkN).2.le hp hε hε1 hδ1⟩

end
end LowRank
