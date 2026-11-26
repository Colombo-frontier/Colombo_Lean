import SampleReuse.DriftCharging
import SecondOrder.IntegralEnergy
import SecondOrder.MartingaleEnergy

/-! Linear drift charging on arbitrary probability spaces. This extends the
finite-law foundation without imposing a second-moment assumption on drift.
The checkpoint intervals in this module are deterministic; stopped checkpoint
reindexing and the sampler-cost coupling are separate remaining obligations. -/

open MeasureTheory Filter SecondOrder
open scoped BigOperators InnerProductSpace

namespace SampleReuse

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [InnerProductSpace ℝ E] in
theorem integrable_truncated_norm {X : Ω → E} (hX : AEStronglyMeasurable X μ)
    (σ L : ℝ) : Integrable (fun w => min (σ ^ 2) (L ^ 2 * ‖X w‖ ^ 2)) μ := by
  have hc : Continuous (fun x : E => min (σ ^ 2) (L ^ 2 * ‖x‖ ^ 2)) :=
    continuous_const.min (continuous_const.mul (continuous_norm.pow 2))
  apply (integrable_const (σ ^ 2)).mono' (hc.comp_aestronglyMeasurable hX)
  filter_upwards [] with w
  rw [Real.norm_of_nonneg (le_min (sq_nonneg σ) (by positivity))]
  exact min_le_left _ _

theorem integral_truncated_interval {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a z : ι → Ω → E) {σ L : ℝ} (hσ : 0 ≤ σ) (hL : 0 ≤ L)
    (ha : ∀ k ∈ s, Integrable (a k) μ) (hz : ∀ k ∈ s, Integrable (z k) μ)
    (hz2 : ∀ k ∈ s, Integrable (fun w => ‖z k w‖ ^ 2) μ)
    (ho : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (∫ w, ⟪z i w, z j w⟫_ℝ ∂μ) = 0) :
    (∫ w, min (σ ^ 2) (L ^ 2 * ‖∑ k ∈ s, (a k w + z k w)‖ ^ 2) ∂μ) ≤
      2 * σ * L * (∑ k ∈ s, ∫ w, ‖a k w‖ ∂μ) +
      2 * L ^ 2 * (∑ k ∈ s, ∫ w, ‖z k w‖ ^ 2 ∂μ) := by
  have hsum := integrable_finset_sum s (fun k hk => (ha k hk).add (hz k hk))
  have hcap := integrable_truncated_norm hsum.aestronglyMeasurable σ L
  have hD := integrable_finset_sum s (fun k hk => (ha k hk).norm)
  have hV := integrable_norm_sum_sq s z hz hz2
  have hb := integral_mono hcap ((hD.const_mul (2 * σ * L)).add (hV.const_mul (2 * L ^ 2)))
    (fun w => truncated_sum_increment s (fun k => a k w) (fun k => z k w) hσ hL)
  simp only [Pi.add_apply] at hb
  rw [integral_add (hD.const_mul _) (hV.const_mul _), integral_const_mul, integral_const_mul,
    integral_finset_sum s (fun k hk => (ha k hk).norm),
    integral_orthogonal_sum_sq s z hz hz2 ho] at hb
  exact hb

theorem integral_truncated_overlap {ι t : Type*} [Fintype ι] [Fintype t] [DecidableEq t]
    (I : ι → Finset t) (depth : ℕ) (a z : t → Ω → E) {σ L : ℝ}
    (hσ : 0 ≤ σ) (hL : 0 ≤ L)
    (ha : ∀ k, Integrable (a k) μ) (hz : ∀ k, Integrable (z k) μ)
    (hz2 : ∀ k, Integrable (fun w => ‖z k w‖ ^ 2) μ)
    (ho : ∀ i j, i ≠ j → (∫ w, ⟪z i w, z j w⟫_ℝ ∂μ) = 0)
    (hdepth : ∀ k, (Finset.univ.filter (fun i => k ∈ I i)).card ≤ depth) :
    (∫ w, ∑ i, min (σ ^ 2) (L ^ 2 * ‖∑ k ∈ I i, (a k w + z k w)‖ ^ 2) ∂μ) ≤
      2 * (depth : ℝ) * (σ * L * (∫ w, ∑ k, ‖a k w‖ ∂μ) +
        L ^ 2 * (∫ w, ∑ k, ‖z k w‖ ^ 2 ∂μ)) := by
  have hcap (i : ι) := integrable_truncated_norm
    (integrable_finset_sum (I i) (fun k _ => (ha k).add (hz k))).aestronglyMeasurable σ L
  simp only [Pi.add_apply] at hcap
  rw [integral_finset_sum Finset.univ (fun i _ => hcap i)]
  have hb := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    integral_truncated_interval (I i) a z hσ hL (fun k _ => ha k) (fun k _ => hz k)
      (fun k _ => hz2 k) (fun j _ k _ hne => ho j k hne))
  have hd := bounded_overlap_sum I depth hdepth (fun k => ∫ w, ‖a k w‖ ∂μ)
    (fun k => integral_nonneg (fun _ => norm_nonneg _))
  have hv := bounded_overlap_sum I depth hdepth (fun k => ∫ w, ‖z k w‖ ^ 2 ∂μ)
    (fun k => integral_nonneg (fun _ => sq_nonneg _))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hb
  rw [integral_finset_sum Finset.univ (fun k _ => (ha k).norm),
    integral_finset_sum Finset.univ (fun k _ => hz2 k)]
  simp only [Finset.sum_add_distrib]
  nlinarith [mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ 2 * σ * L),
    mul_le_mul_of_nonneg_left hv (by positivity : 0 ≤ 2 * L ^ 2)]

theorem integral_truncated_dyadic (M depth : ℕ) (a z : Fin M → Ω → E)
    {σ L : ℝ} (hσ : 0 ≤ σ) (hL : 0 ≤ L)
    (ha : ∀ k, Integrable (a k) μ) (hz : ∀ k, Integrable (z k) μ)
    (hz2 : ∀ k, Integrable (fun w => ‖z k w‖ ^ 2) μ)
    (ho : ∀ i j, i ≠ j → (∫ w, ⟪z i w, z j w⟫_ℝ ∂μ) = 0) :
    (∫ w, ∑ i : Fin depth × Fin M,
      min (σ ^ 2) (L ^ 2 * ‖∑ k ∈ dyadicBlock M i.1.val i.2, (a k w + z k w)‖ ^ 2) ∂μ) ≤
      2 * (depth : ℝ) * (σ * L * (∫ w, ∑ k, ‖a k w‖ ∂μ) +
        L ^ 2 * (∫ w, ∑ k, ‖z k w‖ ^ 2 ∂μ)) :=
  integral_truncated_overlap (fun i : Fin depth × Fin M => dyadicBlock M i.1.val i.2)
    depth a z hσ hL ha hz hz2 ho dyadic_overlap

/-- A genuine conditional-mean-zero hypothesis supplies the orthogonality
needed in the preceding result; it is not an assumed final energy bound. -/
theorem integral_truncated_dyadic_martingale [CompleteSpace E]
    (M depth : ℕ) (a z : Fin M → Ω → E) {σ L : ℝ} (hσ : 0 ≤ σ) (hL : 0 ≤ L)
    (ha : ∀ k, Integrable (a k) μ) (hz : ∀ k, MemLp (z k) 2 μ)
    (past : Fin M → MeasurableSpace Ω) (hp : ∀ j, past j ≤ ‹MeasurableSpace Ω›)
    (hadapt : ∀ i j, i < j → AEStronglyMeasurable[past j] (z i) μ)
    (hzero : ∀ j, μ[z j | past j] =ᵐ[μ] (fun _ => 0)) :
    (∫ w, ∑ i : Fin depth × Fin M,
      min (σ ^ 2) (L ^ 2 * ‖∑ k ∈ dyadicBlock M i.1.val i.2, (a k w + z k w)‖ ^ 2) ∂μ) ≤
      2 * (depth : ℝ) * (σ * L * (∫ w, ∑ k, ‖a k w‖ ∂μ) +
        L ^ 2 * (∫ w, ∑ k, ‖z k w‖ ^ 2 ∂μ)) :=
  integral_truncated_dyadic M depth a z hσ hL ha
    (fun k => (hz k).integrable (by norm_num))
    (fun k => (memLp_two_iff_integrable_sq_norm (hz k).1).mp (hz k))
    (martingale_differences_orthogonal z past hp hz hadapt hzero)

end SampleReuse
