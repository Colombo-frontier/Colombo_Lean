import HeavyTail.Erasure
import Mathlib.Probability.Independence.Basic

/-! The source's simultaneous independent Bernoulli mask law.  A `false`
coordinate is revealed with probability `α`; a `true` coordinate is erased.
This is a product of actual two-point probability measures. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace HeavyTail.IndependentBernoulli
noncomputable section

def maskLaw (k : ℕ) (α : ℝ) (hα : 0 ≤ α) : Measure (Fin k → Bool) :=
  Measure.pi (fun _ : Fin k => (erasureCoin (1 - α) (by linarith)).toMeasure)

instance maskLaw_probability (k : ℕ) (α : ℝ) (hα : 0 ≤ α) :
    IsProbabilityMeasure (maskLaw k α hα) := by
  unfold maskLaw
  infer_instance

theorem maskLaw_coordinate {k : ℕ} (α : ℝ) (hα : 0 ≤ α) (j : Fin k) :
    (maskLaw k α hα).map (fun b => b j) =
      (erasureCoin (1 - α) (by linarith)).toMeasure := by
  classical
  ext s hs
  rw [Measure.map_apply (measurable_pi_apply j) hs]
  have heq : (fun b : Fin k → Bool => b j) ⁻¹' s =
      Set.univ.pi (Function.update (fun _ : Fin k => Set.univ) j s) := by
    ext b
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left]
    constructor
    · intro hb i
      by_cases hi : i = j
      · subst i; simpa only [Function.update_same] using hb
      · rw [Function.update_noteq hi]; exact Set.mem_univ _
    · intro hb
      simpa only [Function.update_same] using hb j
  rw [heq, maskLaw, Measure.pi_pi]
  rw [Finset.prod_eq_single j]
  · simp only [Function.update_same]
  · intro i _ hij
    rw [Function.update_noteq hij, measure_univ]
  · simp

theorem maskLaw_independent {k : ℕ} (α : ℝ) (hα : 0 ≤ α) :
    iIndepFun (fun j (b : Fin k → Bool) => b j) (maskLaw k α hα) := by
  apply (iIndepFun_iff_map_fun_eq_pi_map
    (fun j => (measurable_pi_apply j).aemeasurable)).mpr
  simp only [maskLaw_coordinate]
  change (maskLaw k α hα).map id = maskLaw k α hα
  exact Measure.map_id

theorem coordinate_integral {k : ℕ} (α : ℝ) (hα : 0 ≤ α) (j : Fin k)
    (f : Bool → ℝ) :
    (∫ b, f (b j) ∂maskLaw k α hα) =
      ∫ b, f b ∂(erasureCoin (1 - α) (by linarith)).toMeasure := by
  rw [← maskLaw_coordinate α hα j]
  exact (integral_map (measurable_pi_apply j).aemeasurable
    (Measurable.of_discrete : Measurable f).aestronglyMeasurable).symm

theorem coordinate_unbiased {k : ℕ} {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (g : ℝ) (j : Fin k) :
    (∫ b, erasureReply (1 - α) g (b j) ∂maskLaw k α hα.le) = g := by
  rw [coordinate_integral]
  exact erasure_unbiased (by linarith) (by linarith) g

theorem coordinate_centered {k : ℕ} {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (g : ℝ) (j : Fin k) :
    (∫ b, (erasureReply (1 - α) g (b j) - g) ∂maskLaw k α hα.le) = 0 := by
  rw [integral_sub Integrable.of_finite (integrable_const _), coordinate_unbiased hα hα1,
    integral_const, measureReal_univ_eq_one, one_smul, sub_self]

theorem erasure_coordinate_moment {α p : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hp : 1 ≤ p) (g : ℝ) :
    (∫ b, |erasureReply (1 - α) g b - g| ^ p
      ∂(erasureCoin (1 - α) (by linarith)).toMeasure) ≤
        2 * |g| ^ p * α ^ (1 - p) := by
  rw [erasure_centered_moment (by linarith : 0 < 1 - α) (by linarith)]
  have hαp : α ^ (p - 1) ≤ 1 := Real.rpow_le_one hα.le hα1.le (by linarith)
  have hαp0 : 0 < α ^ (p - 1) := Real.rpow_pos_of_pos hα _
  have hup : (1 - α) ^ p ≤ 1 := Real.rpow_le_one (by linarith) (by linarith) (by linarith)
  have hid : α ^ (1 - p) = 1 / α ^ (p - 1) := by
    rw [show 1 - p = -(p - 1) by ring, Real.rpow_neg hα.le, one_div]
  have hbracket : 1 - α + (1 - α) ^ p / α ^ (p - 1) ≤ 2 / α ^ (p - 1) := by
    apply (le_div_iff₀ hαp0).mpr
    rw [add_mul, div_mul_cancel₀ _ hαp0.ne']
    have hm := mul_le_mul_of_nonneg_left hαp (show 0 ≤ 1 - α by linarith)
    nlinarith
  simp only [sub_sub_cancel] at *
  rw [hid]
  have hm := mul_le_mul_of_nonneg_left hbracket (Real.rpow_nonneg (abs_nonneg g) p)
  convert hm using 1 <;> ring

theorem coordinate_moment {k : ℕ} {α p : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hp : 1 ≤ p) (g : ℝ) (j : Fin k) :
    (∫ b, |erasureReply (1 - α) g (b j) - g| ^ p ∂maskLaw k α hα.le) ≤
      2 * |g| ^ p * α ^ (1 - p) := by
  exact (coordinate_integral α hα.le j
    (fun b => |erasureReply (1 - α) g b - g| ^ p)).trans_le
      (erasure_coordinate_moment hα hα1 hp g)

end
end HeavyTail.IndependentBernoulli
