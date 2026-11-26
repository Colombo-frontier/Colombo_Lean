import FreshGradientMinimax.IndependentMoments
import FreshGradientMinimax.Oracle
import Mathlib.Probability.Kernel.Composition.Prod

/-! A minibatch is constructed as independent repeated draws from one fixed
query law, followed by averaging. Mean, finite second moment, and the exact
1/b variance factor are proved for this actual Markov kernel. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory

variable {Q : Type*} [MeasurableSpace Q] {d : ℕ}

def iidSumKernel (K : Kernel Q (Euclid d)) : ℕ → Kernel Q (Euclid d)
  | 0 => Kernel.deterministic (fun _ => 0) measurable_const
  | n + 1 => ((iidSumKernel K n) ×ₖ K).map (fun z : Euclid d × Euclid d => z.1 + z.2)

instance iidSumKernel_markov (K : Kernel Q (Euclid d)) [IsMarkovKernel K] (n : ℕ) :
    IsMarkovKernel (iidSumKernel K n) := by
  induction n with
  | zero => dsimp [iidSumKernel]; infer_instance
  | succ n ih =>
    letI := ih
    exact Kernel.IsMarkovKernel.map _ (measurable_fst.add measurable_snd)

theorem iidSumKernel_succ (K : Kernel Q (Euclid d)) [IsMarkovKernel K] (n : ℕ) (q : Q) :
    iidSumKernel K (n + 1) q =
      Measure.map (fun z : Euclid d × Euclid d => z.1 + z.2) ((iidSumKernel K n q).prod (K q)) := by
  rw [iidSumKernel, Kernel.map_apply _ (measurable_fst.add measurable_snd), Kernel.prod_apply]

theorem iidSumKernel_moments (K : Kernel Q (Euclid d)) [IsMarkovKernel K] (q : Q) (m : Euclid d)
    (hi : Integrable id (K q)) (hm : (∫ r, r ∂K q) = m)
    (hv : Integrable (fun r => ‖r - m‖ ^ 2) (K q)) (n : ℕ) :
    Integrable id (iidSumKernel K n q) ∧
      (∫ r, r ∂iidSumKernel K n q) = (n : ℝ) • m ∧
      Integrable (fun r => ‖r - (n : ℝ) • m‖ ^ 2) (iidSumKernel K n q) ∧
      (∫ r, ‖r - (n : ℝ) • m‖ ^ 2 ∂iidSumKernel K n q) =
        (n : ℝ) * (∫ r, ‖r - m‖ ^ 2 ∂K q) := by
  change Integrable (fun r : Euclid d => r) (K q) at hi
  induction n with
  | zero =>
    simp only [iidSumKernel, Kernel.deterministic_apply, Nat.cast_zero, zero_smul,
      integral_dirac, sub_zero, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_mul, and_true]
    exact ⟨integrable_dirac, trivial, integrable_dirac⟩
  | succ n ih =>
    obtain ⟨his, hms, hvs, hss⟩ := ih
    change Integrable (fun r : Euclid d => r) (iidSumKernel K n q) at his
    have ha : Measurable (fun z : Euclid d × Euclid d => z.1 + z.2) :=
      measurable_fst.add measurable_snd
    have hsadd : Integrable (fun z : Euclid d × Euclid d => z.1 + z.2)
        ((iidSumKernel K n q).prod (K q)) :=
      (integrable_on_product_fst his).add (integrable_on_product_snd hi)
    have hia : Integrable id (iidSumKernel K (n + 1) q) := by
      rw [iidSumKernel_succ]
      exact (integrable_map_measure measurable_id.aestronglyMeasurable ha.aemeasurable).mpr hsadd
    have hma : (∫ r, r ∂iidSumKernel K (n + 1) q) = ((n + 1 : ℕ) : ℝ) • m := by
      rw [iidSumKernel_succ, integral_map (f := fun r : Euclid d => r)
        ha.aemeasurable measurable_id.aestronglyMeasurable]
      have h := independent_sum_mean his hi
      simpa only [id_eq, hms, hm, Nat.cast_add, Nat.cast_one, add_smul, one_smul] using h
    have hic : Integrable (fun r => r - (n : ℝ) • m) (iidSumKernel K n q) :=
      his.sub (integrable_const _)
    have hir : Integrable (fun r => r - m) (K q) := hi.sub (integrable_const _)
    have hzc : (∫ r, r - (n : ℝ) • m ∂iidSumKernel K n q) = 0 := by
      rw [integral_sub his (integrable_const _), hms]
      simp
    have hzr : (∫ r, r - m ∂K q) = 0 := by
      rw [integral_sub hi (integrable_const _), hm]
      simp
    have hform (z : Euclid d × Euclid d) :
        z.1 + z.2 - ((n + 1 : ℕ) : ℝ) • m = (z.1 - (n : ℝ) • m) + (z.2 - m) := by
      simp only [Nat.cast_add, Nat.cast_one, add_smul, one_smul]
      abel
    have hvc := independent_sum_square_integrable hic hir hvs hv
    have hva : Integrable (fun r => ‖r - ((n + 1 : ℕ) : ℝ) • m‖ ^ 2) (iidSumKernel K (n + 1) q) := by
      rw [iidSumKernel_succ]
      apply (integrable_map_measure (g := fun r : Euclid d => ‖r - ((n + 1 : ℕ) : ℝ) • m‖ ^ 2)
        ((continuous_id.sub continuous_const).norm.pow 2).aestronglyMeasurable
        ha.aemeasurable).mpr
      simpa only [Function.comp_def, hform] using hvc
    refine ⟨hia, hma, hva, ?_⟩
    rw [iidSumKernel_succ, integral_map (f := fun r : Euclid d => ‖r - ((n + 1 : ℕ) : ℝ) • m‖ ^ 2) ha.aemeasurable
      ((continuous_id.sub continuous_const).norm.pow 2).aestronglyMeasurable]
    simp_rw [hform]
    have hs := independent_sum_second_moment hic hir hvs hv
    rw [hzc, hzr, inner_zero_left, mul_zero, add_zero, hss] at hs
    convert hs using 1
    simp only [Nat.cast_add, Nat.cast_one]
    ring

def batchKernel (K : Kernel Q (Euclid d)) (b : ℕ) : Kernel Q (Euclid d) :=
  (iidSumKernel K b).map (fun r => (b : ℝ)⁻¹ • r)

instance batchKernel_markov (K : Kernel Q (Euclid d)) [IsMarkovKernel K] (b : ℕ) :
    IsMarkovKernel (batchKernel K b) :=
  Kernel.IsMarkovKernel.map _ (measurable_const.smul measurable_id)

theorem batchKernel_moments (K : Kernel Q (Euclid d)) [IsMarkovKernel K] (q : Q) (m : Euclid d)
    (hi : Integrable id (K q)) (hm : (∫ r, r ∂K q) = m)
    (hv : Integrable (fun r => ‖r - m‖ ^ 2) (K q)) {b : ℕ} (hb : 0 < b) :
    Integrable id (batchKernel K b q) ∧ (∫ r, r ∂batchKernel K b q) = m ∧
      Integrable (fun r => ‖r - m‖ ^ 2) (batchKernel K b q) ∧
      (∫ r, ‖r - m‖ ^ 2 ∂batchKernel K b q) = (∫ r, ‖r - m‖ ^ 2 ∂K q) / b := by
  obtain ⟨his, hms, hvs, hss⟩ := iidSumKernel_moments K q m hi hm hv b
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hb
  have ha : Measurable (fun r : Euclid d => (b : ℝ)⁻¹ • r) := measurable_const.smul measurable_id
  have he : batchKernel K b q = (iidSumKernel K b q).map (fun r => (b : ℝ)⁻¹ • r) :=
    Kernel.map_apply _ ha q
  have hform (r : Euclid d) : ‖(b : ℝ)⁻¹ • r - m‖ ^ 2 =
      (b : ℝ)⁻¹ ^ 2 * ‖r - (b : ℝ) • m‖ ^ 2 := by
    rw [show (b : ℝ)⁻¹ • r - m = (b : ℝ)⁻¹ • (r - (b : ℝ) • m) by
      simp [smul_sub, smul_smul, hb0], norm_smul_sq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [he]
    exact (integrable_map_measure measurable_id.aestronglyMeasurable ha.aemeasurable).mpr
      (his.smul (b : ℝ)⁻¹)
  · rw [he, integral_map (f := fun r : Euclid d => r) ha.aemeasurable
      measurable_id.aestronglyMeasurable, integral_smul, hms]
    simp [smul_smul, hb0]
  · rw [he]
    apply (integrable_map_measure (g := fun r : Euclid d => ‖r - m‖ ^ 2)
      ((continuous_id.sub continuous_const).norm.pow 2).aestronglyMeasurable
      ha.aemeasurable).mpr
    simpa only [Function.comp_def, hform] using hvs.const_mul ((b : ℝ)⁻¹ ^ 2)
  · rw [he, integral_map (f := fun r : Euclid d => ‖r - m‖ ^ 2) ha.aemeasurable
      ((continuous_id.sub continuous_const).norm.pow 2).aestronglyMeasurable]
    simp_rw [hform]
    rw [integral_const_mul, hss]
    field_simp
    ring

theorem batchKernel_variance_le (K : Kernel Q (Euclid d)) [IsMarkovKernel K]
    (q : Q) (m : Euclid d) {V : ℝ} (hi : Integrable id (K q)) (hm : (∫ r, r ∂K q) = m)
    (hv : Integrable (fun r => ‖r - m‖ ^ 2) (K q))
    (hV : (∫ r, ‖r - m‖ ^ 2 ∂K q) ≤ V) {b : ℕ} (hb : 0 < b) :
    (∫ r, ‖r - m‖ ^ 2 ∂batchKernel K b q) ≤ V / b := by
  rw [(batchKernel_moments K q m hi hm hv hb).2.2.2]
  exact div_le_div_of_nonneg_right hV (Nat.cast_nonneg _)

end FreshGradientMinimax
