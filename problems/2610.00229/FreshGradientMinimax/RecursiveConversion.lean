import FreshGradientMinimax.RecursiveGeometry

/-! Lemma F.4 with actual unconditional Bochner expectations. The base
function, its minimizers, and the entire sequence may all be random and
dependent. The only accuracy premises are the stated value-gap moments;
the squared-gradient integrability and guarantee are conclusions. -/

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory
open scoped BigOperators
variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} {d : ℕ}

theorem recursive_value_to_gradient {μ H δ : ℝ} (hμ : 0 < μ) (hH : 0 < H)
    (Q : Ω → Euclid d → ℝ) (grad : Ω → Euclid d → Euclid d)
    (model : ∀ ω, SmoothStrongModel (Q ω) (grad ω) μ H)
    (v : ℕ → Ω → Euclid d) (N : ℕ) (hscale : H ≤ recursiveMass μ N)
    (hmeas : Measurable (fun ω => grad ω (v N ω)))
    (hgap : ∀ j ≤ N, Integrable (fun ω => (model ω).recursiveGap hμ (fun i => v i ω) j) ν)
    (hacc : ∀ j ≤ N, (∫ ω, (model ω).recursiveGap hμ (fun i => v i ω) j ∂ν) ≤ recursiveAccuracy μ δ N j) :
    Integrable (fun ω => ‖grad ω (v N ω)‖ ^ 2) ν ∧ (∫ ω, ‖grad ω (v N ω)‖ ^ 2 ∂ν) ≤ δ ^ 2 := by
  let G : ℕ → Ω → ℝ := fun j ω => recursiveMass μ j * (model ω).recursiveGap hμ (fun i => v i ω) j
  let c : ℝ := δ ^ 2 / (10000 * (N + 1 : ℕ) ^ 2)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hGi (j : ℕ) (hj : j ≤ N) : Integrable (G j) ν := (hgap j hj).const_mul _
  have hGb (j : ℕ) (hj : j ≤ N) : (∫ ω, G j ω ∂ν) ≤ c := by
    dsimp only [G]
    rw [integral_const_mul]
    exact (mul_le_mul_of_nonneg_left (hacc j hj) (recursiveMass_pos hμ j).le).trans_eq
      (recursiveAccuracy_scaled hμ δ N j)
  have hsi (j : ℕ) (hj : j ∈ Finset.range N) : Integrable (fun ω => 8 * G j ω + 4 * G (j + 1) ω) ν :=
    ((hGi j (Nat.le_of_lt (Finset.mem_range.mp hj))).const_mul 8).add
      ((hGi (j + 1) (Finset.mem_range.mp hj)).const_mul 4)
  have hsum := integrable_finset_sum (Finset.range N) hsi
  let W : Ω → ℝ := fun ω => (N + 1 : ℕ) * (4 * G N ω +
    ∑ j ∈ Finset.range N, (8 * G j ω + 4 * G (j + 1) ω))
  have hWi : Integrable W ν := (((hGi N le_rfl).const_mul 4).add hsum).const_mul _
  have hpoint (ω : Ω) : ‖grad ω (v N ω)‖ ^ 2 ≤ W ω :=
    (model ω).recursive_gradient_scaled_gap_bound hμ hH (fun i => v i ω) N hscale
  have hi : Integrable (fun ω => ‖grad ω (v N ω)‖ ^ 2) ν := by
    apply hWi.mono' (hmeas.norm.pow_const 2).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hpoint ω)
  have hWb : (∫ ω, W ω ∂ν) ≤ (N + 1 : ℕ) * (4 * c + (N : ℝ) * (12 * c)) := by
    dsimp only [W]
    rw [integral_const_mul, integral_add ((hGi N le_rfl).const_mul 4) hsum,
      integral_const_mul, integral_finset_sum _ hsi]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply add_le_add (mul_le_mul_of_nonneg_left (hGb N le_rfl) (by norm_num))
    calc
      _ ≤ ∑ j ∈ Finset.range N, 12 * c := by
        apply Finset.sum_le_sum
        intro j hj
        rw [integral_add ((hGi j (Nat.le_of_lt (Finset.mem_range.mp hj))).const_mul 8)
          ((hGi (j + 1) (Finset.mem_range.mp hj)).const_mul 4), integral_const_mul 8 (G j),
          integral_const_mul 4 (G (j + 1))]
        have hjb := hGb j (Nat.le_of_lt (Finset.mem_range.mp hj))
        have hjb' := hGb (j + 1) (Finset.mem_range.mp hj)
        linarith
      _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  refine ⟨hi, ((integral_mono hi hWi hpoint).trans hWb).trans ?_⟩
  have hN : (0 : ℝ) < (N + 1 : ℕ) := by positivity
  calc
    _ ≤ (N + 1 : ℕ) * (12 * (N + 1 : ℕ) * c) := by push_cast; nlinarith only [hc, hN]
    _ = (12 / 10000 : ℝ) * δ ^ 2 := by dsimp [c]; push_cast; field_simp; ring
    _ ≤ δ ^ 2 := by nlinarith [sq_nonneg δ]

theorem recursive_value_to_gradient_log_stages {μ H δ : ℝ} (hμ : 0 < μ) (hμH : μ ≤ H)
    (Q : Ω → Euclid d → ℝ) (grad : Ω → Euclid d → Euclid d)
    (model : ∀ ω, SmoothStrongModel (Q ω) (grad ω) μ H)
    (v : ℕ → Ω → Euclid d)
    (hmeas : Measurable (fun ω => grad ω (v (recursiveLastIndex H μ) ω)))
    (hgap : ∀ j ≤ recursiveLastIndex H μ,
      Integrable (fun ω => (model ω).recursiveGap hμ (fun i => v i ω) j) ν)
    (hacc : ∀ j ≤ recursiveLastIndex H μ,
      (∫ ω, (model ω).recursiveGap hμ (fun i => v i ω) j ∂ν) ≤ recursiveAccuracy μ δ (recursiveLastIndex H μ) j) :
    Integrable (fun ω => ‖grad ω (v (recursiveLastIndex H μ) ω)‖ ^ 2) ν ∧
      (∫ ω, ‖grad ω (v (recursiveLastIndex H μ) ω)‖ ^ 2 ∂ν) ≤ δ ^ 2 :=
  recursive_value_to_gradient hμ (hμ.trans_le hμH) Q grad model v _
    (recursiveLastIndex_mass hμ hμH).1 hmeas hgap hacc

end FreshGradientMinimax
