import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Tactic

namespace RandomizedFO2003

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The quantitative principal-angle step in Lemma highmult. -/
theorem stable_decomposition (k v : E)
    (hangle : |inner (𝕜 := ℝ) k v| ≤ (1 / 2 : ℝ) * ‖k‖ * ‖v‖) :
    ‖k‖ + ‖v‖ ≤ 2 * ‖k + v‖ := by
  have hinner := (abs_le.mp hangle).1
  have hnorm := norm_add_sq_real k v
  have hsquare := sq_nonneg (‖k‖ - ‖v‖)
  have hnonneg := norm_nonneg (k + v)
  have hsum : 0 ≤ ‖k‖ + ‖v‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith

/-- A readout nearly orthogonal to both summands is small on their sum. -/
theorem readout_on_sum (a k v : E) (δ η : ℝ)
    (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (hk : |inner (𝕜 := ℝ) a k| ≤ δ * ‖k‖)
    (hv : |inner (𝕜 := ℝ) a v| ≤ η * ‖v‖)
    (hangle : |inner (𝕜 := ℝ) k v| ≤ (1 / 2 : ℝ) * ‖k‖ * ‖v‖) :
    |inner (𝕜 := ℝ) a (k + v)| ≤ 2 * (δ + η) * ‖k + v‖ := by
  rw [inner_add_right]
  have hdec := stable_decomposition k v hangle
  calc
    |inner (𝕜 := ℝ) a k + inner (𝕜 := ℝ) a v|
        ≤ |inner (𝕜 := ℝ) a k| + |inner (𝕜 := ℝ) a v| := abs_add _ _
    _ ≤ δ * ‖k‖ + η * ‖v‖ := add_le_add hk hv
    _ ≤ (δ + η) * (‖k‖ + ‖v‖) := by
      nlinarith [mul_nonneg hδ (norm_nonneg v), mul_nonneg hη (norm_nonneg k)]
    _ ≤ (δ + η) * (2 * ‖k + v‖) :=
      mul_le_mul_of_nonneg_left hdec (add_nonneg hδ hη)
    _ = 2 * (δ + η) * ‖k + v‖ := by ring

theorem radial_preserves_information (S : Submodule ℝ E) (z : E) (r : ℝ)
    (hz : z ∈ S) : r • z ∈ S := S.smul_mem r hz

/-- The actual radial map can be substituted once its norm and radial-form facts are proved. -/
theorem squashed_readout_bound
    (S : Submodule ℝ E) (a z : E) (r B α₀ c : ℝ)
    (hz : z ∈ S) (hα₀ : 0 < α₀) (hc : 0 ≤ c)
    (hsmall : ∀ y ∈ S, |inner (𝕜 := ℝ) a y| ≤ c * ‖y‖)
    (hsquash : ‖r • z‖ ≤ 2 * B) (hmargin : c * (2 * B) ≤ α₀ / 4) :
    |inner (𝕜 := ℝ) a (r • z) / α₀| ≤ 1 / 4 := by
  rw [abs_div, abs_of_pos hα₀]
  apply (div_le_iff₀ hα₀).mpr
  calc
    |inner (𝕜 := ℝ) a (r • z)| ≤ c * ‖r • z‖ :=
      hsmall _ (radial_preserves_information S z r hz)
    _ ≤ c * (2 * B) := mul_le_mul_of_nonneg_left hsquash hc
    _ ≤ α₀ / 4 := hmargin
    _ = 1 / 4 * α₀ := by ring

end RandomizedFO2003
