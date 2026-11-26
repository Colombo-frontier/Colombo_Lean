import MatchingBounds1005.SequentialKernelKL
import MatchingBounds1005.KernelKLIntegrability

/-!
# From deterministic cumulative conditional KL to transcript KL

Uniform one-step bounds ensure likelihood integrability. The final estimate
retains the cumulative cost along each actual history, so no extra factor of
the number of steps is introduced when a telescoping energy bound is used.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory
open scoped BigOperators ENNReal NNReal

namespace MatchingBounds1005.SequentialKLBound
open KernelKL KernelKLIntegrability SequentialKernelKL

variable {Y : Type} [MeasurableSpace Y]

def cumulativeCost (cost : (n : ℕ) → History Y n → ℝ) : (n : ℕ) → History Y n → ℝ
  | 0, _ => 0
  | n + 1, h => cumulativeCost cost n h.1 + cost n h.1

theorem cumulativeCost_nonneg (cost : (n : ℕ) → History Y n → ℝ)
    (hc : ∀ n h, 0 ≤ cost n h) (n : ℕ) (h : History Y n) :
    0 ≤ cumulativeCost cost n h := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact add_nonneg (ih h.1) (hc n h.1)

variable (κ η : (n : ℕ) → Kernel (History Y n) Y)
variable [∀ n, IsMarkovKernel (κ n)] [∀ n, IsMarkovKernel (η n)]

theorem cumulativeCost_integrable (cost : (n : ℕ) → History Y n → ℝ)
    (hi : ∀ n, Integrable (cost n) (transcriptLaw κ n)) (n : ℕ) :
    Integrable (cumulativeCost cost n) (transcriptLaw κ n) := by
  induction n with
  | zero => exact integrable_zero _ _ _
  | succ n ih =>
      have hfst : MeasurePreserving (Prod.fst : History Y n × Y → History Y n)
          (transcriptLaw κ n ⊗ₘ κ n) (transcriptLaw κ n) :=
        ⟨measurable_fst, Measure.fst_compProd _ _⟩
      exact (hfst.integrable_comp (ih.add (hi n)).aestronglyMeasurable).mpr (ih.add (hi n))

theorem integral_cumulativeCost (cost : (n : ℕ) → History Y n → ℝ)
    (hi : ∀ n, Integrable (cost n) (transcriptLaw κ n)) (n : ℕ) :
    (∫ h, cumulativeCost cost n h ∂transcriptLaw κ n) =
      ∑ t ∈ Finset.range n, ∫ h, cost t h ∂transcriptLaw κ t := by
  induction n with
  | zero => simp [cumulativeCost]
  | succ n ih =>
      have hLift := cumulativeCost_integrable κ cost hi (n + 1)
      change Integrable (fun h : History Y n × Y => cumulativeCost cost n h.1 + cost n h.1)
        (transcriptLaw κ n ⊗ₘ κ n) at hLift
      change (∫ h : History Y n × Y, cumulativeCost cost n h.1 + cost n h.1
        ∂(transcriptLaw κ n ⊗ₘ κ n)) = _
      rw [Measure.integral_compProd hLift]
      simp only [integral_const, measureReal_univ_eq_one, one_smul]
      rw [integral_add (cumulativeCost_integrable κ cost hi n) (hi n), ih,
        Finset.sum_range_succ]

def conditionalCost (n : ℕ) (h : History Y n) : ℝ := (klDiv (κ n h) (η n h)).toReal

variable [MeasurableSpace.CountablyGenerated Y]

theorem conditionalCost_measurable (hAC : ∀ n h, κ n h ≪ η n h) (n : ℕ) :
    StronglyMeasurable (conditionalCost κ η n) := by
  have heq : (fun h => ∫ y, kernelLLR (κ n) (η n) (h, y) ∂κ n h) =
      conditionalCost κ η n := funext (integral_kernelLLR (κ n) (η n) (hAC n))
  rw [← heq]
  exact (kernelLLR_measurable (κ n) (η n)).stronglyMeasurable.integral_kernel_prod_right'

theorem conditionalCost_integrable_of_bound (C : ℕ → ℝ≥0)
    (hc : ∀ n h, klDiv (κ n h) (η n h) ≤ ENNReal.ofReal (C n)) (n : ℕ) :
    Integrable (conditionalCost κ η n) (transcriptLaw κ n) := by
  have hAC : ∀ n h, κ n h ≪ η n h := fun n h =>
    (klDiv_ne_top_iff.mp (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hc n h))).1
  apply (integrable_const (C n : ℝ)).mono' (conditionalCost_measurable κ η hAC n).aestronglyMeasurable
  exact ae_of_all _ (fun h => by
    dsimp only [conditionalCost]
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    simpa only [ENNReal.toReal_ofReal (C n).coe_nonneg] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top (hc n h))

/-- Exact expected cumulative conditional KL, with the side integrability
proved from actual one-step KL bounds. -/
theorem transcriptLaw_klDiv_eq_integral (C : ℕ → ℝ≥0)
    (hc : ∀ n h, klDiv (κ n h) (η n h) ≤ ENNReal.ofReal (C n)) (n : ℕ) :
    klDiv (transcriptLaw κ n) (transcriptLaw η n) =
      ENNReal.ofReal (∫ h, cumulativeCost (conditionalCost κ η) n h ∂transcriptLaw κ n) := by
  have hAC : ∀ n h, κ n h ≪ η n h := fun n h =>
    (klDiv_ne_top_iff.mp (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hc n h))).1
  have hi : ∀ n, Integrable (kernelLLR (κ n) (η n)) (transcriptLaw κ n ⊗ₘ κ n) :=
    fun n => integrable_kernelLLR_of_bounded_kl (κ n) (η n) (transcriptLaw κ n)
      (C n) (C n).coe_nonneg (hc n)
  rw [transcriptLaw_klDiv κ η hAC hi n,
    integral_cumulativeCost κ (conditionalCost κ η) (conditionalCost_integrable_of_bound κ η C hc) n]
  have hn (t : ℕ) : 0 ≤ ∫ h, conditionalCost κ η t h ∂transcriptLaw κ t :=
    integral_nonneg (fun _ => ENNReal.toReal_nonneg)
  rw [ENNReal.ofReal_sum_of_nonneg (fun t _ => hn t)]
  rfl

/-- A deterministic cumulative cost cap controls the actual adaptive
transcript KL, with no multiplicative horizon loss. -/
theorem transcriptLaw_klDiv_le_cumulative (C : ℕ → ℝ≥0)
    (hc : ∀ n h, klDiv (κ n h) (η n h) ≤ ENNReal.ofReal (C n))
    (n : ℕ) (cap : ℝ) (hcap : ∀ h, cumulativeCost (conditionalCost κ η) n h ≤ cap) :
    klDiv (transcriptLaw κ n) (transcriptLaw η n) ≤ ENNReal.ofReal cap := by
  rw [transcriptLaw_klDiv_eq_integral κ η C hc n]
  apply ENNReal.ofReal_le_ofReal
  calc
    (∫ h, cumulativeCost (conditionalCost κ η) n h ∂transcriptLaw κ n) ≤
        ∫ _h, cap ∂transcriptLaw κ n :=
      integral_mono (cumulativeCost_integrable κ (conditionalCost κ η)
        (conditionalCost_integrable_of_bound κ η C hc) n) (integrable_const cap) hcap
    _ = cap := by simp

end MatchingBounds1005.SequentialKLBound
