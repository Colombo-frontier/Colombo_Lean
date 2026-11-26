import HeavyTail.Erasure
import HeavyTail.AdaptiveSamplerTesting
import HeavyTail.GaussianLowerGeometry

/-! A finite one-coordinate revelation law. Each coordinate is revealed with
probability pi; the remaining mass produces the zero response. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal InnerProductSpace
namespace HeavyTail.MaskedLower
noncomputable section

def CoordinateMask (k : ℕ) := Option (Fin k)
instance {k : ℕ} : Fintype (CoordinateMask k) := inferInstanceAs (Fintype (Option (Fin k)))
instance {k : ℕ} : DecidableEq (CoordinateMask k) := inferInstanceAs (DecidableEq (Option (Fin k)))
instance {k : ℕ} : MeasurableSpace (CoordinateMask k) := ⊤

def coordinateWeight {k : ℕ} (π : ℝ) : CoordinateMask k → ℝ
  | none => 1 - (k : ℝ) * π
  | some _ => π

theorem coordinateWeight_nonneg {k : ℕ} {π : ℝ} (hπ : 0 ≤ π)
    (hkπ : (k : ℝ) * π ≤ 1) (b : CoordinateMask k) : 0 ≤ coordinateWeight π b := by
  cases b with
  | none => exact sub_nonneg.mpr hkπ
  | some j => exact hπ

theorem coordinateWeight_sum {k : ℕ} (π : ℝ) :
    ∑ b : CoordinateMask k, coordinateWeight π b = 1 := by
  change (∑ b : Option (Fin k), coordinateWeight π b) = 1
  simp [Fintype.sum_option, coordinateWeight]

def coordinateCoin {k : ℕ} (π : ℝ) (hπ : 0 ≤ π) (hkπ : (k : ℝ) * π ≤ 1) :
    PMF (CoordinateMask k) :=
  PMF.ofFintype (fun b => ENNReal.ofReal (coordinateWeight π b)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun b _ => coordinateWeight_nonneg hπ hkπ b),
      coordinateWeight_sum]
    norm_num)

theorem coordinate_expectation {k : ℕ} {π : ℝ} (hπ : 0 ≤ π)
    (hkπ : (k : ℝ) * π ≤ 1) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : CoordinateMask k → E) :
    (∫ b, f b ∂(coordinateCoin π hπ hkπ).toMeasure) =
      (1 - (k : ℝ) * π) • f none + ∑ j : Fin k, π • f (some j) := by
  rw [PMF.integral_eq_sum]
  simp only [coordinateCoin, PMF.ofFintype_apply,
    ENNReal.toReal_ofReal (coordinateWeight_nonneg hπ hkπ _)]
  change (∑ b : Option (Fin k), coordinateWeight π b • f b) = _
  rw [Fintype.sum_option]
  rfl

theorem coordinate_no_reveal_probability {k : ℕ} {π : ℝ} (hπ : 0 ≤ π)
    (hkπ : (k : ℝ) * π ≤ 1) (j : Fin k) :
    (coordinateCoin π hπ hkπ).toMeasure.real {b | b ≠ some j} = 1 - π := by
  have hmass : (coordinateCoin π hπ hkπ).toMeasure.real {some j} = π := by
    rw [measureReal_def, PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _)]
    exact ENNReal.toReal_ofReal hπ
  have hs : MeasurableSet ({some j} : Set (CoordinateMask k)) := MeasurableSet.of_discrete
  have hsum := measureReal_add_measureReal_compl
    (μ := (coordinateCoin π hπ hkπ).toMeasure) hs
  rw [hmass, measureReal_univ_eq_one] at hsum
  change (coordinateCoin π hπ hkπ).toMeasure.real ({some j}ᶜ) = _
  linarith

theorem no_reveal_all_calls_lower {T : ℕ} {π : ℝ} (hπ : π ≤ 1)
    (hbudget : (T : ℝ) * π ≤ 1 / 8) : (7 / 8 : ℝ) ≤ (1 - π) ^ T := by
  have h := one_add_mul_le_pow (a := -π) (by linarith : -2 ≤ -π) T
  simp only [mul_neg, add_neg_cancel_left, ← sub_eq_add_neg] at h
  linarith

end
end HeavyTail.MaskedLower
