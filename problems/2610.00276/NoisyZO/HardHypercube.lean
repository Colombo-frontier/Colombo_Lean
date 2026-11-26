import NoisyZO.SmoothCutoff
import NoisyZO.AssouadReduction
import NoisyZO.AssouadTesting
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Embedding Boolean hypercube vertices into the hard function family

The Assouad layer indexes models by Boolean vectors, while the analytic hard
family uses real signs.  This file proves that these two encodings commute
with a coordinate flip and transfers the global signal bound to arbitrary
adaptive queries.
-/

open scoped BigOperators

namespace NoisyZO

noncomputable section

instance pointMeasurableSpace (d : ℕ) : MeasurableSpace (Point d) :=
  borel (Point d)

instance pointBorelSpace (d : ℕ) : BorelSpace (Point d) :=
  ⟨rfl⟩

def hypercubeSign {d : ℕ} (s : Hypercube d) : Fin d → ℝ :=
  fun i ↦ boolSign (s i)

@[simp] theorem hypercubeSign_sq {d : ℕ} (s : Hypercube d) (i : Fin d) :
    hypercubeSign s i ^ 2 = 1 := by
  cases h : s i <;> simp [hypercubeSign, boolSign, h]

theorem hypercubeSign_flip {d : ℕ} (s : Hypercube d) (i : Fin d) :
    hypercubeSign (flipHypercube s i) = flip (hypercubeSign s) i := by
  funext j
  by_cases hji : j = i
  · subst j
    cases h : s i <;> simp [hypercubeSign, flipHypercube, flip, boolSign, h]
  · simp [hypercubeSign, flipHypercube, flip, boolSign, hji]

/-- The Gaussian response mean obtained by evaluating a hard-family member at
the query selected from the current history. -/
def hardGaussianMean {α : Type*} {d : ℕ}
    (c h : ℝ) (hh : 0 < h) (query : ℕ → α → Point d)
    (s : Hypercube d) (t : ℕ) (a : α) : ℝ :=
  hardValue (radialCutoff d h hh) (c / Real.sqrt d)
    (hypercubeSign s) (query t a)

theorem hardGaussianMean_measurable
    {α : Type*} [MeasurableSpace α] {d : ℕ}
    (c h : ℝ) (hh : 0 < h) (query : ℕ → α → Point d)
    (hquery : ∀ t, Measurable (query t)) (s : Hypercube d) (t : ℕ) :
    Measurable (hardGaussianMean c h hh query s t) := by
  exact (hardValue_continuous
    (ContDiff.continuous (radialCutoff_contDiff (n := ⊤) d h hh))
    (c / Real.sqrt d) (hypercubeSign s)).measurable.comp (hquery t)

/-- The manuscript's summed neighboring-signal bound, now for the actual
Boolean hard family and for an arbitrary history-dependent query. -/
theorem hardGaussianMean_signal_sum_le
    {α : Type*} {d : ℕ} (hd : 0 < d)
    (c h : ℝ) (hh : 0 < h) (query : ℕ → α → Point d)
    (s : Hypercube d) (t : ℕ) (a : α) :
    (∑ i : Fin d,
      (hardGaussianMean c h hh query s t a -
        hardGaussianMean c h hh query (flipHypercube s i) t a) ^ 2) ≤
      4 * c ^ 2 * h ^ 2 / d := by
  unfold hardGaussianMean
  simp_rw [hypercubeSign_flip]
  exact normalized_summed_neighbor_signal_radialCutoff_le hd c h hh
    (hypercubeSign s) (hypercubeSign_sq s) (query t a)

end

end NoisyZO
