import LowRank.MinimumDimensionCubicUpper

/-! Replace tolerance-dependent logarithms by one explicit logarithm of
a polynomial in the smaller dimension, rank, and inverse accuracy. -/

namespace LowRank
open Matrix
open scoped ENNReal
noncomputable section
universe u

theorem confidentRitzTolerance_reciprocal_le {k s d : ℕ} {γ ε : ℝ}
    (hk : 0 < k) (hs : 0 < s) (hγ : 0 < γ) (hε : 0 < ε)
    (hwidth : (s : ℝ) * ε ≤ 14 * (k : ℝ)) (hgap : ε ≤ (k : ℝ) * γ) :
    2 / confidentRitzTolerance γ (40 * (k : ℝ)) s d ≤
      1024 * (k : ℝ) ^ 2 * ((d : ℝ) + 1) / ε := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  let D : ℝ := 2 * (40 * (k : ℝ)) ^ 2 * (s : ℝ) * ((d : ℝ) + 1)
  let B : ℝ := 1024 * (k : ℝ) ^ 2 * ((d : ℝ) + 1) / ε
  let η := confidentRitzTolerance γ (40 * (k : ℝ)) s d
  have hD : 0 < D := by dsimp [D]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hη : 0 < η := confidentRitzTolerance_pos hγ (by positivity) hs
  have hηsq : η ^ 2 = γ / D := Real.sq_sqrt (div_nonneg hγ.le hD.le)
  have hηD : η ^ 2 * D = γ := by rw [hηsq]; exact div_mul_cancel₀ _ hD.ne'
  have hd1 : 1 ≤ (d : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg d)
  have hc : 179200 * ((d : ℝ) + 1) ≤ 1048576 * ((d : ℝ) + 1) ^ 2 := by nlinarith
  have hbudget : 4 * D ≤ γ * B ^ 2 := by
    apply (mul_le_mul_right (pow_pos hε 2)).mp
    calc
      4 * D * ε ^ 2 = (12800 * (k : ℝ) ^ 2 * ((d : ℝ) + 1) * ε) * ((s : ℝ) * ε) := by
        dsimp [D]
        ring
      _ ≤ (12800 * (k : ℝ) ^ 2 * ((d : ℝ) + 1) * ε) * (14 * (k : ℝ)) :=
        mul_le_mul_of_nonneg_left hwidth (by positivity)
      _ = (179200 * (k : ℝ) ^ 3 * ((d : ℝ) + 1)) * ε := by ring
      _ ≤ (179200 * (k : ℝ) ^ 3 * ((d : ℝ) + 1)) * ((k : ℝ) * γ) :=
        mul_le_mul_of_nonneg_left hgap (by positivity)
      _ = ((k : ℝ) ^ 4 * γ) * (179200 * ((d : ℝ) + 1)) := by ring
      _ ≤ ((k : ℝ) ^ 4 * γ) * (1048576 * ((d : ℝ) + 1) ^ 2) :=
        mul_le_mul_of_nonneg_left hc (by positivity)
      _ = γ * B ^ 2 * ε ^ 2 := by dsimp [B]; field_simp; ring
  have hsq : 4 ≤ (η * B) ^ 2 := by
    apply (mul_le_mul_right hD).mp
    calc
      4 * D ≤ γ * B ^ 2 := hbudget
      _ = (η * B) ^ 2 * D := by rw [← hηD]; ring
  have hprod : 2 ≤ η * B := by nlinarith [mul_pos hη hB]
  exact (div_le_iff₀ hη).mpr (by nlinarith)

def cubicPolylog (N k : ℕ) (ε : ℝ) : ℝ :=
  73 + 72 * Real.log (1024 * (k : ℝ) ^ 2 * ((N : ℝ) + 1) / ε)

theorem minimumDimensionLogFactor_le_polylog {N k : ℕ} {ε : ℝ}
    (hk : 0 < k) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    minimumDimensionLogFactor N k ε ≤ cubicPolylog N k ε := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkR : 0 < (k : ℝ) := by linarith
  have ha := accuracyScale_ge_one hε hε1
  have has : accuracyScale ε * ε ≤ 1 := by
    rw [mul_comm, ← cubicKrylovGap_eq_mul_scale hε]
    exact cubicKrylovGap_le_one hε.le hε1
  have hwidthN : ((2 * k + 2 : ℕ) : ℝ) * ε ≤ 14 * (k : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hε1 (Nat.cast_nonneg (2 * k + 2))
    push_cast at h ⊢
    nlinarith
  have hwidthW : ((2 * wideKrylovRank k ε + 2 : ℕ) : ℝ) * ε ≤ 14 * (k : ℝ) := by
    calc
      _ ≤ (14 * ((k : ℝ) * accuracyScale ε)) * ε :=
        mul_le_mul_of_nonneg_right (wideKrylovBlockWidth_le hk hε hε1) hε.le
      _ = (14 * (k : ℝ)) * (accuracyScale ε * ε) := by ring
      _ ≤ (14 * (k : ℝ)) * 1 := mul_le_mul_of_nonneg_left has (by positivity)
      _ = _ := by ring
  have hgapN : ε ≤ (k : ℝ) * cubicKrylovGap ε := by
    have hka : 1 ≤ (k : ℝ) * accuracyScale ε := one_le_mul_of_one_le_of_one_le hk1 ha
    calc
      ε ≤ ε * ((k : ℝ) * accuracyScale ε) := le_mul_of_one_le_right hε.le hka
      _ = _ := by rw [cubicKrylovGap_eq_mul_scale hε]; ring
  have hgapW : ε ≤ (k : ℝ) * (ε / (k : ℝ)) := by
    have he : (k : ℝ) * (ε / (k : ℝ)) = ε := by field_simp
    exact le_of_eq he.symm
  have hN := confidentRitzTolerance_reciprocal_le (d := N) hk (by omega : 0 < 2 * k + 2)
    (cubicKrylovGap_pos hε) hε hwidthN hgapN
  have hW := confidentRitzTolerance_reciprocal_le (d := N) hk
    (by omega : 0 < 2 * wideKrylovRank k ε + 2) (div_pos hε hkR) hε hwidthW hgapW
  change 2 / cubicNarrowTolerance N k ε ≤ _ at hN
  change 2 / cubicWideTolerance N k ε ≤ _ at hW
  have hNp := (cubicNarrowTolerance_bounds (a := N) hk hε hε1).1
  have hWp := (cubicWideTolerance_bounds (a := N) hk hε hε1).1
  have hn := Real.log_le_log (by positivity : 0 < 2 / cubicNarrowTolerance N k ε) hN
  have hw := Real.log_le_log (by positivity : 0 < 2 / cubicWideTolerance N k ε) hW
  unfold minimumDimensionLogFactor cubicQueryLogFactor cubicPolylog
  linarith

theorem rectangularQueryComplexity_le_explicit_polylog {a b k : ℕ}
    (hk0 : 0 < k) (hka : k ≤ a) (hkb : k ≤ b)
    {p ε δ : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : δ ≤ 19 / 20) :
    rectangularQueryComplexity.{u} a b k p ε δ ≤
      ENNReal.ofReal (cubicPolylog (min a b) k ε * targetRate (min a b) k ε) := by
  apply (rectangularQueryComplexity_le_minimum_dimension_rate hk0 hka hkb hp hp2 hε hε1 hδ).trans
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_right (minimumDimensionLogFactor_le_polylog hk0 hε hε1)
  exact le_min (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg k) (accuracyScale_pos hε).le)

theorem rectangularQueryComplexity_two_sided_explicit_polylog {p : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ (a b k : ℕ) (ε δ : ℝ),
      0 < k → k < min a b → 0 < ε → ε ≤ 1 → 1 / 5 ≤ δ → δ ≤ 19 / 20 →
      ENNReal.ofReal (c * targetRate (min a b) k ε) ≤ rectangularQueryComplexity.{u} a b k p ε δ ∧
      rectangularQueryComplexity.{u} a b k p ε δ ≤
        ENNReal.ofReal (cubicPolylog (min a b) k ε * targetRate (min a b) k ε) := by
  obtain ⟨c, hc, hlow⟩ := rectangularQueryComplexity_rate.{u} (by linarith : 0 < p)
  refine ⟨c, hc, ?_⟩
  intro a b k ε δ hk hkN hε hε1 hδ hδ1
  exact ⟨hlow a b k ε δ hk hkN hε hε1 hδ,
    rectangularQueryComplexity_le_explicit_polylog hk (lt_min_iff.mp hkN).1.le
      (lt_min_iff.mp hkN).2.le hp hp2 hε hε1 hδ1⟩

end
end LowRank
