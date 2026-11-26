import MatchingBounds1005.KernelKL

/-!
# Finite adaptive likelihood and KL accumulation

The transcript measure is defined recursively by actual Markov
composition-products. Transition kernels may depend on the complete previous
transcript. The KL sum is proved by induction from the verified kernel chain
rule; it is not an assumed abstract information-cost recurrence.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory
open scoped BigOperators ENNReal NNReal

namespace MatchingBounds1005.SequentialKernelKL
open KernelKL

def History (Y : Type) : ℕ → Type
  | 0 => Unit
  | n + 1 => History Y n × Y

instance historyMeasurableSpace (Y : Type) [MeasurableSpace Y] (n : ℕ) :
    MeasurableSpace (History Y n) :=
  match n with
  | 0 => inferInstanceAs (MeasurableSpace Unit)
  | n + 1 =>
      letI := historyMeasurableSpace Y n
      inferInstanceAs (MeasurableSpace (History Y n × Y))

variable {Y : Type} [MeasurableSpace Y]

def transcriptLaw (κ : (n : ℕ) → Kernel (History Y n) Y) :
    (n : ℕ) → Measure (History Y n)
  | 0 => Measure.dirac ()
  | n + 1 => transcriptLaw κ n ⊗ₘ κ n

instance transcriptLaw_probability (κ : (n : ℕ) → Kernel (History Y n) Y)
    [∀ n, IsMarkovKernel (κ n)] (n : ℕ) : IsProbabilityMeasure (transcriptLaw κ n) := by
  induction n with
  | zero => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac ()))
  | succ n ih =>
      letI := ih
      exact inferInstanceAs (IsProbabilityMeasure ((transcriptLaw κ n) ⊗ₘ κ n))

variable (κ η : (n : ℕ) → Kernel (History Y n) Y)
variable [∀ n, IsMarkovKernel (κ n)] [∀ n, IsMarkovKernel (η n)]

theorem transcriptLaw_ac (hκη : ∀ n h, κ n h ≪ η n h) (n : ℕ) :
    transcriptLaw κ n ≪ transcriptLaw η n := by
  induction n with
  | zero => exact Measure.AbsolutelyContinuous.rfl
  | succ n ih => exact ih.compProd (ae_of_all _ (hκη n))

variable [MeasurableSpace.CountablyGenerated Y]

theorem transcriptLaw_llr_integrable (hκη : ∀ n h, κ n h ≪ η n h)
    (hi : ∀ n, Integrable (kernelLLR (κ n) (η n)) (transcriptLaw κ n ⊗ₘ κ n))
    (n : ℕ) : Integrable (llr (transcriptLaw κ n) (transcriptLaw η n)) (transcriptLaw κ n) := by
  induction n with
  | zero =>
      apply (integrable_congr (llr_self (Measure.dirac ()))).mpr
      exact integrable_zero _ _ _
  | succ n ih =>
      have hfst : MeasurePreserving (Prod.fst : History Y n × Y → History Y n)
          (transcriptLaw κ n ⊗ₘ κ n) (transcriptLaw κ n) :=
        ⟨measurable_fst, Measure.fst_compProd _ _⟩
      have hfirst : Integrable (fun p : History Y n × Y =>
          llr (transcriptLaw κ n) (transcriptLaw η n) p.1) (transcriptLaw κ n ⊗ₘ κ n) :=
        (hfst.integrable_comp ih.aestronglyMeasurable).mpr ih
      exact (hfirst.add (hi n)).congr
        (compProd_llr (κ n) (η n) (transcriptLaw_ac κ η hκη n) (hκη n)).symm

def expectedStepKL (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (∫ h, (klDiv (κ n h) (η n h)).toReal ∂transcriptLaw κ n)

/-- Exact finite KL accumulation for genuinely adaptive transition kernels.
All likelihood integrability conditions concern the constructed transcript
laws themselves. -/
theorem transcriptLaw_klDiv (hκη : ∀ n h, κ n h ≪ η n h)
    (hi : ∀ n, Integrable (kernelLLR (κ n) (η n)) (transcriptLaw κ n ⊗ₘ κ n))
    (n : ℕ) : klDiv (transcriptLaw κ n) (transcriptLaw η n) =
      ∑ t ∈ Finset.range n, expectedStepKL κ η t := by
  induction n with
  | zero => simp [transcriptLaw]
  | succ n ih =>
      change klDiv (transcriptLaw κ n ⊗ₘ κ n) (transcriptLaw η n ⊗ₘ η n) = _
      rw [klDiv_compProd (κ n) (η n) (transcriptLaw_ac κ η hκη n) (hκη n)
        (transcriptLaw_llr_integrable κ η hκη hi n) (hi n), ih, Finset.sum_range_succ]
      rfl

theorem transcriptLaw_klDiv_le (hκη : ∀ n h, κ n h ≪ η n h)
    (hi : ∀ n, Integrable (kernelLLR (κ n) (η n)) (transcriptLaw κ n ⊗ₘ κ n))
    (n : ℕ) (cost : ℕ → ℝ≥0∞)
    (hc : ∀ t < n, expectedStepKL κ η t ≤ cost t) :
    klDiv (transcriptLaw κ n) (transcriptLaw η n) ≤ ∑ t ∈ Finset.range n, cost t := by
  rw [transcriptLaw_klDiv κ η hκη hi n]
  exact Finset.sum_le_sum (fun t ht => hc t (Finset.mem_range.mp ht))

end MatchingBounds1005.SequentialKernelKL
