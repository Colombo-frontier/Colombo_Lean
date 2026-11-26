import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.Variance
import Mathlib.Tactic

/-! # Square-integrable Hilbert-valued noise sums -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace BigOperators
namespace NCBall

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {μ : Measure Ω}

theorem integrable_inner_of_memLp {f g : Ω → E} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun ω => ⟪f ω, g ω⟫_ℝ) μ := by
  apply (L2.integrable_inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)).congr
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with ω hfw hgw
  rw [hfw, hgw]

theorem integral_sq_norm_add_of_orthogonal {f g : Ω → E}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (ho : (∫ ω, ⟪f ω, g ω⟫_ℝ ∂μ) = 0) :
    (∫ ω, ‖f ω + g ω‖ ^ 2 ∂μ) = (∫ ω, ‖f ω‖ ^ 2 ∂μ) + ∫ ω, ‖g ω‖ ^ 2 ∂μ := by
  have hi := integrable_inner_of_memLp hf hg
  have ha : Integrable (fun ω => ‖f ω‖ ^ 2 + 2 * ⟪f ω, g ω⟫_ℝ) μ :=
    hf.norm.integrable_sq.add (hi.const_mul 2)
  calc
    _ = ∫ ω, (‖f ω‖ ^ 2 + 2 * ⟪f ω, g ω⟫_ℝ) + ‖g ω‖ ^ 2 ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun ω => norm_add_sq_real (f ω) (g ω))
    _ = _ := by
      rw [integral_add ha hg.norm.integrable_sq,
        integral_add hf.norm.integrable_sq (hi.const_mul 2), integral_const_mul, ho]
      ring

theorem integral_sq_norm_sum_of_orthogonal (e : ℕ → Ω → E)
    (he : ∀ t, MemLp (e t) 2 μ)
    (ho : ∀ i j, i < j → (∫ ω, ⟪e i ω, e j ω⟫_ℝ ∂μ) = 0) (N : ℕ) :
    (∫ ω, ‖∑ t ∈ Finset.range N, e t ω‖ ^ 2 ∂μ) =
      ∑ t ∈ Finset.range N, ∫ ω, ‖e t ω‖ ^ 2 ∂μ := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hs : MemLp (fun ω => ∑ t ∈ Finset.range N, e t ω) 2 μ :=
      memLp_finset_sum _ (fun t _ => he t)
    have hz : (∫ ω, ⟪∑ t ∈ Finset.range N, e t ω, e N ω⟫_ℝ ∂μ) = 0 := by
      simp only [sum_inner]
      rw [integral_finset_sum _ (fun t _ => integrable_inner_of_memLp (he t) (he N))]
      exact Finset.sum_eq_zero (fun t ht => ho t N (Finset.mem_range.mp ht))
    simp only [Finset.sum_range_succ]
    rw [integral_sq_norm_add_of_orthogonal hs (he N) hz, ih]

omit [InnerProductSpace ℝ E] in
theorem integral_norm_sq_le_second_moment [IsProbabilityMeasure μ] {f : Ω → E}
    (hf : MemLp f 2 μ) :
    (∫ ω, ‖f ω‖ ∂μ) ^ 2 ≤ ∫ ω, ‖f ω‖ ^ 2 ∂μ := by
  have hv := variance_nonneg (fun ω => ‖f ω‖) μ
  rw [variance_def' hf.norm] at hv
  exact sub_nonneg.mp hv

theorem integral_norm_noise_sum_le [IsProbabilityMeasure μ] (e : ℕ → Ω → E)
    (he : ∀ t, MemLp (e t) 2 μ)
    (ho : ∀ i j, i < j → (∫ ω, ⟪e i ω, e j ω⟫_ℝ ∂μ) = 0)
    {V : ℝ} (hV : ∀ t, (∫ ω, ‖e t ω‖ ^ 2 ∂μ) ≤ V ^ 2) (N : ℕ) :
    (∫ ω, ‖∑ t ∈ Finset.range N, e t ω‖ ∂μ) ≤ Real.sqrt (N : ℝ) * |V| := by
  have hs : MemLp (fun ω => ∑ t ∈ Finset.range N, e t ω) 2 μ :=
    memLp_finset_sum _ (fun t _ => he t)
  have hm := integral_norm_sq_le_second_moment hs
  rw [integral_sq_norm_sum_of_orthogonal e he ho N] at hm
  have hv : (∑ t ∈ Finset.range N, ∫ ω, ‖e t ω‖ ^ 2 ∂μ) ≤ (N : ℝ) * V ^ 2 := by
    calc
      _ ≤ ∑ _t ∈ Finset.range N, V ^ 2 := Finset.sum_le_sum (fun t _ => hV t)
      _ = _ := by simp
  have hsqrt : (Real.sqrt (N : ℝ) * |V|) ^ 2 = (N : ℝ) * V ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg N), sq_abs]
  have hnorm : 0 ≤ ∫ ω, ‖∑ t ∈ Finset.range N, e t ω‖ ∂μ :=
    integral_nonneg (fun ω => norm_nonneg (∑ t ∈ Finset.range N, e t ω))
  nlinarith [hnorm,
    mul_nonneg (Real.sqrt_nonneg (N : ℝ)) (abs_nonneg V)]

end NCBall
