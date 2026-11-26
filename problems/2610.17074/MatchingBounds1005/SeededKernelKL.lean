import MatchingBounds1005.SequentialPosterior
import MatchingBounds1005.KernelKLIntegrability

/-!
# Adaptive KL with the complete independent seed retained

Both experiments start with the same arbitrary seed law. Their finite
transcripts retain that seed and every raw scalar response. The exact KL
chain rule and cumulative bound therefore apply to the joint law appearing
in the manuscript, not merely to a transcript with a deterministic seed.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory
open scoped BigOperators ENNReal NNReal

namespace MatchingBounds1005.SeededKernelKL
open SequentialPosterior KernelKL KernelKLIntegrability

variable {Ω : Type*} [MeasurableSpace Ω] {T : ℕ}

def transcriptLaw (κ : (n : ℕ) → Kernel (History Ω T n) (Fin T → ℝ)) (ν₀ : Measure Ω) :
    (n : ℕ) → Measure (History Ω T n)
  | 0 => ν₀
  | n + 1 => transcriptLaw κ ν₀ n ⊗ₘ κ n

instance transcriptLaw_probability (κ : (n : ℕ) → Kernel (History Ω T n) (Fin T → ℝ))
    [∀ n, IsMarkovKernel (κ n)] (ν₀ : Measure Ω) [IsProbabilityMeasure ν₀] (n : ℕ) :
    IsProbabilityMeasure (transcriptLaw κ ν₀ n) := by
  induction n with
  | zero => exact inferInstanceAs (IsProbabilityMeasure ν₀)
  | succ n ih =>
      letI := ih
      exact inferInstanceAs (IsProbabilityMeasure ((transcriptLaw κ ν₀ n) ⊗ₘ κ n))

variable (κ η : (n : ℕ) → Kernel (History Ω T n) (Fin T → ℝ))
variable [∀ n, IsMarkovKernel (κ n)] [∀ n, IsMarkovKernel (η n)]
variable (ν₀ : Measure Ω) [IsProbabilityMeasure ν₀]

theorem transcriptLaw_ac (hAC : ∀ n h, κ n h ≪ η n h) (n : ℕ) :
    transcriptLaw κ ν₀ n ≪ transcriptLaw η ν₀ n := by
  induction n with
  | zero => exact Measure.AbsolutelyContinuous.rfl
  | succ n ih => exact ih.compProd (ae_of_all _ (hAC n))

theorem transcriptLaw_llr_integrable (hAC : ∀ n h, κ n h ≪ η n h)
    (hi : ∀ n, Integrable (kernelLLR (κ n) (η n)) (transcriptLaw κ ν₀ n ⊗ₘ κ n))
    (n : ℕ) : Integrable (llr (transcriptLaw κ ν₀ n) (transcriptLaw η ν₀ n))
      (transcriptLaw κ ν₀ n) := by
  induction n with
  | zero =>
      apply (integrable_congr (llr_self ν₀)).mpr
      exact integrable_zero _ _ _
  | succ n ih =>
      have hfst : MeasurePreserving (Prod.fst : History Ω T n × (Fin T → ℝ) → History Ω T n)
          (transcriptLaw κ ν₀ n ⊗ₘ κ n) (transcriptLaw κ ν₀ n) :=
        ⟨measurable_fst, Measure.fst_compProd _ _⟩
      have hfirst : Integrable (fun p : History Ω T n × (Fin T → ℝ) =>
          llr (transcriptLaw κ ν₀ n) (transcriptLaw η ν₀ n) p.1)
          (transcriptLaw κ ν₀ n ⊗ₘ κ n) :=
        (hfst.integrable_comp ih.aestronglyMeasurable).mpr ih
      exact (hfirst.add (hi n)).congr
        (compProd_llr (κ n) (η n) (transcriptLaw_ac κ η ν₀ hAC n) (hAC n)).symm

def conditionalCost (n : ℕ) (h : History Ω T n) : ℝ := (klDiv (κ n h) (η n h)).toReal

def cumulativeCost (cost : (n : ℕ) → History Ω T n → ℝ) : (n : ℕ) → History Ω T n → ℝ
  | 0, _ => 0
  | n + 1, h => cumulativeCost cost n h.1 + cost n h.1

theorem transcriptLaw_klDiv (hAC : ∀ n h, κ n h ≪ η n h)
    (hi : ∀ n, Integrable (kernelLLR (κ n) (η n)) (transcriptLaw κ ν₀ n ⊗ₘ κ n))
    (n : ℕ) : klDiv (transcriptLaw κ ν₀ n) (transcriptLaw η ν₀ n) =
      ∑ t ∈ Finset.range n, ENNReal.ofReal (∫ h, conditionalCost κ η t h ∂transcriptLaw κ ν₀ t) := by
  induction n with
  | zero => simp [transcriptLaw]
  | succ n ih =>
      change klDiv (transcriptLaw κ ν₀ n ⊗ₘ κ n) (transcriptLaw η ν₀ n ⊗ₘ η n) = _
      rw [klDiv_compProd (κ n) (η n) (transcriptLaw_ac κ η ν₀ hAC n) (hAC n)
        (transcriptLaw_llr_integrable κ η ν₀ hAC hi n) (hi n), ih, Finset.sum_range_succ]
      rfl

theorem cumulativeCost_integrable (cost : (n : ℕ) → History Ω T n → ℝ)
    (hi : ∀ n, Integrable (cost n) (transcriptLaw κ ν₀ n)) (n : ℕ) :
    Integrable (cumulativeCost cost n) (transcriptLaw κ ν₀ n) := by
  induction n with
  | zero => exact integrable_zero _ _ _
  | succ n ih =>
      have hfst : MeasurePreserving (Prod.fst : History Ω T n × (Fin T → ℝ) → History Ω T n)
          (transcriptLaw κ ν₀ n ⊗ₘ κ n) (transcriptLaw κ ν₀ n) :=
        ⟨measurable_fst, Measure.fst_compProd _ _⟩
      exact (hfst.integrable_comp (ih.add (hi n)).aestronglyMeasurable).mpr (ih.add (hi n))

theorem integral_cumulativeCost (cost : (n : ℕ) → History Ω T n → ℝ)
    (hi : ∀ n, Integrable (cost n) (transcriptLaw κ ν₀ n)) (n : ℕ) :
    (∫ h, cumulativeCost cost n h ∂transcriptLaw κ ν₀ n) =
      ∑ t ∈ Finset.range n, ∫ h, cost t h ∂transcriptLaw κ ν₀ t := by
  induction n with
  | zero => simp [cumulativeCost]
  | succ n ih =>
      have hLift := cumulativeCost_integrable κ ν₀ cost hi (n + 1)
      change Integrable (fun h : History Ω T n × (Fin T → ℝ) =>
        cumulativeCost cost n h.1 + cost n h.1) (transcriptLaw κ ν₀ n ⊗ₘ κ n) at hLift
      change (∫ h : History Ω T n × (Fin T → ℝ), cumulativeCost cost n h.1 + cost n h.1
        ∂(transcriptLaw κ ν₀ n ⊗ₘ κ n)) = _
      rw [Measure.integral_compProd hLift]
      simp only [integral_const, measureReal_univ_eq_one, one_smul]
      rw [integral_add (cumulativeCost_integrable κ ν₀ cost hi n) (hi n), ih,
        Finset.sum_range_succ]

theorem conditionalCost_integrable (C : ℕ → ℝ≥0)
    (hc : ∀ n h, klDiv (κ n h) (η n h) ≤ ENNReal.ofReal (C n)) (n : ℕ) :
    Integrable (conditionalCost κ η n) (transcriptLaw κ ν₀ n) := by
  have hAC : ∀ n h, κ n h ≪ η n h := fun n h =>
    (klDiv_ne_top_iff.mp (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hc n h))).1
  have heq : (fun h => ∫ y, kernelLLR (κ n) (η n) (h, y) ∂κ n h) =
      conditionalCost κ η n := funext (integral_kernelLLR (κ n) (η n) (hAC n))
  have hm : StronglyMeasurable (conditionalCost κ η n) := by
    rw [← heq]
    exact (kernelLLR_measurable (κ n) (η n)).stronglyMeasurable.integral_kernel_prod_right'
  apply (integrable_const (C n : ℝ)).mono' hm.aestronglyMeasurable
  exact ae_of_all _ (fun h => by
    dsimp only [conditionalCost]
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    simpa only [ENNReal.toReal_ofReal (C n).coe_nonneg] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top (hc n h))

/-- Actual KL for the common-seed joint transcript equals expected
cumulative conditional KL; integrability is proved from finite local bounds. -/
theorem transcriptLaw_klDiv_eq_integral (C : ℕ → ℝ≥0)
    (hc : ∀ n h, klDiv (κ n h) (η n h) ≤ ENNReal.ofReal (C n)) (n : ℕ) :
    klDiv (transcriptLaw κ ν₀ n) (transcriptLaw η ν₀ n) =
      ENNReal.ofReal (∫ h, cumulativeCost (conditionalCost κ η) n h ∂transcriptLaw κ ν₀ n) := by
  have hAC : ∀ n h, κ n h ≪ η n h := fun n h =>
    (klDiv_ne_top_iff.mp (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hc n h))).1
  have hi : ∀ n, Integrable (kernelLLR (κ n) (η n)) (transcriptLaw κ ν₀ n ⊗ₘ κ n) :=
    fun n => integrable_kernelLLR_of_bounded_kl (κ n) (η n) (transcriptLaw κ ν₀ n)
      (C n) (C n).coe_nonneg (hc n)
  rw [transcriptLaw_klDiv κ η ν₀ hAC hi n,
    integral_cumulativeCost κ ν₀ (conditionalCost κ η) (conditionalCost_integrable κ η ν₀ C hc) n]
  have hn (t : ℕ) : 0 ≤ ∫ h, conditionalCost κ η t h ∂transcriptLaw κ ν₀ t :=
    integral_nonneg (fun _ => ENNReal.toReal_nonneg)
  rw [ENNReal.ofReal_sum_of_nonneg (fun t _ => hn t)]

theorem transcriptLaw_klDiv_le_cumulative (C : ℕ → ℝ≥0)
    (hc : ∀ n h, klDiv (κ n h) (η n h) ≤ ENNReal.ofReal (C n))
    (n : ℕ) (cap : ℝ) (hcap : ∀ h, cumulativeCost (conditionalCost κ η) n h ≤ cap) :
    klDiv (transcriptLaw κ ν₀ n) (transcriptLaw η ν₀ n) ≤ ENNReal.ofReal cap := by
  rw [transcriptLaw_klDiv_eq_integral κ η ν₀ C hc n]
  apply ENNReal.ofReal_le_ofReal
  calc
    (∫ h, cumulativeCost (conditionalCost κ η) n h ∂transcriptLaw κ ν₀ n) ≤
        ∫ _h, cap ∂transcriptLaw κ ν₀ n :=
      integral_mono (cumulativeCost_integrable κ ν₀ (conditionalCost κ η)
        (conditionalCost_integrable κ η ν₀ C hc) n) (integrable_const cap) hcap
    _ = cap := by simp

end MatchingBounds1005.SeededKernelKL
