import LowRank.GraphProjector
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Entrywise expectations preserve positivity and Loewner order. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix BigOperators

variable {Ω n : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [Fintype n] [DecidableEq n]

noncomputable def matrixMean (μ : Measure Ω) (A : Ω → Matrix n n ℝ) : Matrix n n ℝ :=
  fun i j => ∫ ω, A ω i j ∂μ

def EntryIntegrable (A : Ω → Matrix n n ℝ) (μ : Measure Ω) : Prop :=
  ∀ i j, Integrable (fun ω => A ω i j) μ

theorem integral_quadratic {A : Ω → Matrix n n ℝ} (hA : EntryIntegrable A μ)
    (v : n → ℝ) :
    (∫ ω, v ⬝ᵥ (A ω *ᵥ v) ∂μ) = v ⬝ᵥ (matrixMean μ A *ᵥ v) := by
  simp only [dotProduct, mulVec]
  simp_rw [Finset.mul_sum]
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _
    (fun j _ => ((hA i j).mul_const (v j)).const_mul (v i)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finset_sum _ (fun j _ => ((hA i j).mul_const (v j)).const_mul (v i))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul, integral_mul_const]
  rfl

theorem matrixMean_posSemidef {A : Ω → Matrix n n ℝ}
    (hA : EntryIntegrable A μ) (hpsd : ∀ᵐ ω ∂μ, (A ω).PosSemidef) :
    (matrixMean μ A).PosSemidef := by
  constructor
  · rw [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial]
    ext i j
    apply integral_congr_ae
    filter_upwards [hpsd] with ω hω
    have h := hω.isHermitian.eq
    simpa only [conjTranspose_eq_transpose_of_trivial] using congrFun (congrFun h i) j
  · intro v
    simp only [star_trivial]
    rw [← integral_quadratic hA]
    apply integral_nonneg_of_ae
    filter_upwards [hpsd] with ω hω
    simpa using hω.2 v

theorem matrixMean_sub {A B : Ω → Matrix n n ℝ}
    (hA : EntryIntegrable A μ) (hB : EntryIntegrable B μ) :
    matrixMean μ (fun ω => A ω - B ω) = matrixMean μ A - matrixMean μ B := by
  ext i j
  exact integral_sub (hA i j) (hB i j)

theorem matrixMean_mono {A B : Ω → Matrix n n ℝ}
    (hA : EntryIntegrable A μ) (hB : EntryIntegrable B μ)
    (hAB : ∀ᵐ ω ∂μ, LoewnerLE (A ω) (B ω)) :
    LoewnerLE (matrixMean μ A) (matrixMean μ B) := by
  have h : (matrixMean μ (fun ω => B ω - A ω)).PosSemidef :=
    matrixMean_posSemidef (fun i j => (hB i j).sub (hA i j)) hAB
  rw [matrixMean_sub hB hA] at h
  exact h

theorem matrixMean_trace {A : Ω → Matrix n n ℝ} (hA : EntryIntegrable A μ) :
    (matrixMean μ A).trace = ∫ ω, (A ω).trace ∂μ := by
  exact (integral_finset_sum _ (fun i _ => hA i i)).symm

/-- The expectation step of bottom-block covariance. Haar isotropy is an explicit
input `hiso`, to be established from the actual posterior law. -/
theorem mean_bottom_covariance {A Q : Ω → Matrix n n ℝ} {c : ℝ}
    (hA : EntryIntegrable A μ) (hQ : EntryIntegrable Q μ)
    (hdom : ∀ᵐ ω ∂μ, LoewnerLE (A ω) (Q ω))
    (hiso : matrixMean μ Q = c • (1 : Matrix n n ℝ)) :
    LoewnerLE (matrixMean μ A) (c • (1 : Matrix n n ℝ)) := by
  rw [← hiso]
  exact matrixMean_mono hA hQ hdom

end LowRank
