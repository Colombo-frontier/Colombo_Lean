import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Probability.Process.Filtration
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Conditional product concentration

The conditional one-step expectation bounds are inputs. The product expectation
and terminal deviation probability are proved, using the actual conditional
expectation, filtration and probability measure. Integrability of the factors
and finite prefix products is explicit; it is not replaced by a terminal moment
bound. The latter regularity obligations must be checked for each application.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace HeavyTail

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable [IsProbabilityMeasure P]

def prefixProduct (W : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∏ i ∈ Finset.range n, W i ω

theorem prefixProduct_zero (W : ℕ → Ω → ℝ) (ω : Ω) : prefixProduct W 0 ω = 1 := by
  simp [prefixProduct]

theorem prefixProduct_succ (W : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    prefixProduct W (n + 1) ω = prefixProduct W n ω * W n ω := by
  simp [prefixProduct, Finset.prod_range_succ]

theorem prefixProduct_nonneg {W : ℕ → Ω → ℝ}
    (hW : ∀ i ω, 0 ≤ W i ω) (n : ℕ) (ω : Ω) : 0 ≤ prefixProduct W n ω := by
  exact Finset.prod_nonneg (fun i _ => hW i ω)

theorem prefixProduct_pos {W : ℕ → Ω → ℝ}
    (hW : ∀ i ω, 0 < W i ω) (n : ℕ) (ω : Ω) : 0 < prefixProduct W n ω := by
  exact Finset.prod_pos (fun i _ => hW i ω)

/-- The prefix before observation `n` is measurable with respect to its past. -/
theorem prefixProduct_stronglyMeasurable {ℱ : Filtration ℕ mΩ} {W : ℕ → Ω → ℝ}
    (hW : ∀ i, StronglyMeasurable[ℱ (i + 1)] (W i)) (n : ℕ) :
    StronglyMeasurable[ℱ n] (prefixProduct W n) := by
  apply Finset.stronglyMeasurable_prod
  intro i hi
  exact (hW i).mono (ℱ.mono (Nat.succ_le_iff.mpr (Finset.mem_range.mp hi)))

/-- The actual conditional pull-out property yields the one-step integral bound. -/
theorem conditional_product_integral_step {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {X W : Ω → ℝ} {c : ℝ} (hXmeas : StronglyMeasurable[m] X)
    (hXnonneg : ∀ ω, 0 ≤ X ω) (hXint : Integrable X P) (hWint : Integrable W P)
    (hprodint : Integrable (X * W) P)
    (hcond : ∀ᵐ ω ∂P, (P[W | m]) ω ≤ c) :
    (∫ ω, X ω * W ω ∂P) ≤ c * ∫ ω, X ω ∂P := by
  have hpull := condExp_mul_of_stronglyMeasurable_left hXmeas hprodint hWint
  have hle : (P[X * W | m]) ≤ᵐ[P] (fun ω => c * X ω) := by
    filter_upwards [hpull, hcond] with ω heq hbound
    simp only [Pi.mul_apply] at heq
    rw [heq]
    nlinarith [mul_le_mul_of_nonneg_left hbound (hXnonneg ω)]
  have hi := integral_mono_ae integrable_condExp (hXint.const_mul c) hle
  rw [integral_condExp hm, integral_const_mul] at hi
  exact hi

/-- Product moments are derived by conditioning; they are not assumed. -/
theorem prefixProduct_integral_bound {ℱ : Filtration ℕ mΩ} {W : ℕ → Ω → ℝ}
    {c : ℝ} (hc : 0 ≤ c)
    (hWmeas : ∀ i, StronglyMeasurable[ℱ (i + 1)] (W i))
    (hWnonneg : ∀ i ω, 0 ≤ W i ω)
    (hWint : ∀ i, Integrable (W i) P)
    (hprodint : ∀ n, Integrable (prefixProduct W n) P)
    (hcond : ∀ i, ∀ᵐ ω ∂P, (P[W i | ℱ i]) ω ≤ c) (n : ℕ) :
    (∫ ω, prefixProduct W n ω ∂P) ≤ c ^ n := by
  induction n with
  | zero => simp [prefixProduct]
  | succ n ih =>
    have hprod : Integrable (prefixProduct W n * W n) P := by
      have heq : prefixProduct W n * W n = prefixProduct W (n + 1) := by
        funext ω
        exact (prefixProduct_succ W n ω).symm
      rw [heq]
      exact hprodint (n + 1)
    have hstep := conditional_product_integral_step (ℱ.le n)
      (prefixProduct_stronglyMeasurable hWmeas n) (prefixProduct_nonneg hWnonneg n)
      (hprodint n) (hWint n) hprod (hcond n)
    calc
      (∫ ω, prefixProduct W (n + 1) ω ∂P) =
          ∫ ω, prefixProduct W n ω * W n ω ∂P := by simp only [prefixProduct_succ]
      _ ≤ c * ∫ ω, prefixProduct W n ω ∂P := hstep
      _ ≤ c * c ^ n := mul_le_mul_of_nonneg_left ih hc
      _ = c ^ (n + 1) := by ring

/-- Markov's inequality applied to the conditionally controlled product. -/
theorem prefixProduct_tail_bound {ℱ : Filtration ℕ mΩ} {W : ℕ → Ω → ℝ}
    {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ)
    (hWmeas : ∀ i, StronglyMeasurable[ℱ (i + 1)] (W i))
    (hWnonneg : ∀ i ω, 0 ≤ W i ω)
    (hWint : ∀ i, Integrable (W i) P)
    (hprodint : ∀ n, Integrable (prefixProduct W n) P)
    (hcond : ∀ i, ∀ᵐ ω ∂P, (P[W i | ℱ i]) ω ≤ c) (n : ℕ) :
    P.real {ω | c ^ n / δ ≤ prefixProduct W n ω} ≤ δ := by
  have hmean := prefixProduct_integral_bound hc.le hWmeas hWnonneg hWint hprodint hcond n
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (prefixProduct_nonneg hWnonneg n)) (hprodint n) (c ^ n / δ)
  have ht : 0 < c ^ n / δ := div_pos (pow_pos hc n) hδ
  have hid : (c ^ n / δ) * δ = c ^ n := div_mul_cancel₀ _ hδ.ne'
  nlinarith

/-- The logarithmic confidence statement used by the manuscript online lemma. -/
theorem conditional_log_sum_tail {ℱ : Filtration ℕ mΩ} {W : ℕ → Ω → ℝ}
    {ν δ : ℝ} (hδ : 0 < δ)
    (hWmeas : ∀ i, StronglyMeasurable[ℱ (i + 1)] (W i))
    (hWpos : ∀ i ω, 0 < W i ω)
    (hWint : ∀ i, Integrable (W i) P)
    (hprodint : ∀ n, Integrable (prefixProduct W n) P)
    (hcond : ∀ i, ∀ᵐ ω ∂P, (P[W i | ℱ i]) ω ≤ Real.exp ν) (n : ℕ) :
    P.real {ω | (n : ℝ) * ν + Real.log (1 / δ) <
      ∑ i ∈ Finset.range n, Real.log (W i ω)} ≤ δ := by
  have hprod := prefixProduct_tail_bound (Real.exp_pos ν) hδ hWmeas
    (fun i ω => (hWpos i ω).le) hWint hprodint hcond n
  apply le_trans (measureReal_mono (s₂ := {ω | (Real.exp ν) ^ n / δ ≤ prefixProduct W n ω}) ?_) hprod
  intro ω hω
  have hlog : Real.log (prefixProduct W n ω) =
      ∑ i ∈ Finset.range n, Real.log (W i ω) :=
    Real.log_prod _ _ (fun i _ => (hWpos i ω).ne')
  have hexp := Real.exp_lt_exp.mpr hω
  rw [← hlog, Real.exp_log (prefixProduct_pos hWpos n ω), Real.exp_add,
    Real.exp_log (one_div_pos.mpr hδ), Real.exp_nat_mul] at hexp
  change (Real.exp ν) ^ n / δ ≤ prefixProduct W n ω
  simpa only [div_eq_mul_inv, one_mul] using hexp.le

/-- Uniformly bounded factors automatically discharge every integrability premise. -/
theorem conditional_log_sum_tail_of_bounded {ℱ : Filtration ℕ mΩ}
    {W : ℕ → Ω → ℝ} {ν δ B : ℝ} (hδ : 0 < δ)
    (hWmeas : ∀ i, StronglyMeasurable[ℱ (i + 1)] (W i))
    (hWpos : ∀ i ω, 0 < W i ω) (hWbound : ∀ i ω, W i ω ≤ B)
    (hcond : ∀ i, ∀ᵐ ω ∂P, (P[W i | ℱ i]) ω ≤ Real.exp ν) (n : ℕ) :
    P.real {ω | (n : ℝ) * ν + Real.log (1 / δ) <
      ∑ i ∈ Finset.range n, Real.log (W i ω)} ≤ δ := by
  have hWint : ∀ i, Integrable (W i) P := by
    intro i
    refine (integrable_const B).mono' ((hWmeas i).mono (ℱ.le (i + 1))).aestronglyMeasurable ?_
    filter_upwards with ω
    simpa only [Real.norm_eq_abs, abs_of_pos (hWpos i ω)] using hWbound i ω
  have hprodint : ∀ k, Integrable (prefixProduct W k) P := by
    intro k
    refine (integrable_const (B ^ k)).mono'
      ((prefixProduct_stronglyMeasurable hWmeas k).mono (ℱ.le k)).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_pos (prefixProduct_pos hWpos k ω)]
    calc
      prefixProduct W k ω ≤ ∏ _i ∈ Finset.range k, B :=
        Finset.prod_le_prod (fun i _ => (hWpos i ω).le) (fun i _ => hWbound i ω)
      _ = B ^ k := by simp
  exact conditional_log_sum_tail hδ hWmeas hWpos hWint hprodint hcond n

/-- The second product argument in the online proof, for exponential increments. -/
theorem conditional_exponential_sum_tail {ℱ : Filtration ℕ mΩ}
    {Y : ℕ → Ω → ℝ} {ν δ : ℝ} (hδ : 0 < δ)
    (hYmeas : ∀ i, StronglyMeasurable[ℱ (i + 1)] (Y i))
    (hfactorint : ∀ i, Integrable (fun ω => Real.exp (Y i ω)) P)
    (hpartialint : ∀ k, Integrable
      (fun ω => Real.exp (∑ i ∈ Finset.range k, Y i ω)) P)
    (hcond : ∀ i, ∀ᵐ ω ∂P, (P[(fun ω => Real.exp (Y i ω)) | ℱ i]) ω ≤ Real.exp ν)
    (n : ℕ) :
    P.real {ω | (n : ℝ) * ν + Real.log (1 / δ) <
      ∑ i ∈ Finset.range n, Y i ω} ≤ δ := by
  have hprodint : ∀ k, Integrable (prefixProduct (fun i ω => Real.exp (Y i ω)) k) P := by
    intro k
    simpa only [prefixProduct, Real.exp_sum] using hpartialint k
  have h := conditional_log_sum_tail hδ
    (fun i => Real.continuous_exp.comp_stronglyMeasurable (hYmeas i))
    (fun i ω => Real.exp_pos (Y i ω)) hfactorint hprodint hcond n
  simpa only [Real.log_exp] using h

end HeavyTail
