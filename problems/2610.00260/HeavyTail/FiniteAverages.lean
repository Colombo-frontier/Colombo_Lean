import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic

/-! Feasibility and Jensen's inequality for the running average actually stored
by the composite stage. These include the initially empty accumulator. -/
noncomputable section
open Set
namespace HeavyTail
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def runningAverage (k : ℕ) (s : E) : E := (k : ℝ)⁻¹ • s

theorem runningAverage_add {k : ℕ} (hk : 0 < k) (s y : E) :
    runningAverage (k + 1) (s + y) =
      ((k : ℝ) / (k + 1)) • runningAverage k s + (1 / ((k : ℝ) + 1)) • y := by
  have hk0 : (k : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hk)
  unfold runningAverage
  push_cast
  rw [smul_add, smul_smul]
  have he : (k : ℝ) / (k + 1) * (k : ℝ)⁻¹ = ((k : ℝ) + 1)⁻¹ := by
    field_simp
    ring
  rw [he, one_div]

theorem runningAverage_next_mem {S : Set E} (hS : Convex ℝ S) {k : ℕ} {s y : E}
    (hzero : k = 0 → s = 0) (havg : 0 < k → runningAverage k s ∈ S) (hy : y ∈ S) :
    runningAverage (k + 1) (s + y) ∈ S := by
  by_cases hk : k = 0
  · simpa [hk, hzero hk, runningAverage] using hy
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    rw [runningAverage_add hkpos]
    apply hS (havg hkpos) hy (by positivity) (by positivity)
    have hkp : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    field_simp

theorem runningAverage_next_convex_bound {S : Set E} {F : E → ℝ} (hF : ConvexOn ℝ S F)
    {k : ℕ} {s y : E} (hzero : k = 0 → s = 0)
    (havg : 0 < k → runningAverage k s ∈ S) (hy : y ∈ S) :
    ((k : ℝ) + 1) * F (runningAverage (k + 1) (s + y)) ≤
      (k : ℝ) * F (runningAverage k s) + F y := by
  by_cases hk : k = 0
  · simp [hk, hzero hk, runningAverage]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have hkp : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hs : (k : ℝ) / (k + 1) + 1 / ((k : ℝ) + 1) = 1 := by field_simp
    have hh := hF.2 (havg hkpos) hy (by positivity : 0 ≤ (k : ℝ) / (k + 1))
      (by positivity : 0 ≤ 1 / ((k : ℝ) + 1)) hs
    rw [← runningAverage_add hkpos] at hh
    simp only [smul_eq_mul] at hh
    have he : (k : ℝ) / (k + 1) * F (runningAverage k s) +
        1 / ((k : ℝ) + 1) * F y = ((k : ℝ) * F (runningAverage k s) + F y) / (k + 1) := by ring
    rw [he] at hh
    have hb := (le_div_iff₀ hkp).mp hh
    nlinarith only [hb]

end HeavyTail
