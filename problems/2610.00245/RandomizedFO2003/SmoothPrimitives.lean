import RandomizedFO2003.SmoothSaturation
import RandomizedFO2003.RadialGate

namespace RandomizedFO2003.Primitives

open Set

universe u

/-- A common numerical derivative constant, chosen before the radius,
saturation threshold, and underlying inner product space. -/
theorem smooth_primitive_derivative_bounds (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧
      (∀ x : ℝ, |iteratedDeriv k gate x| ≤ C) ∧
      (2 ≤ k → ∀ K x : ℝ, |iteratedDeriv k (saturation K) x| ≤ C) ∧
      ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E],
        ∀ B : ℝ, 0 < B → ∀ x : E,
          ‖iteratedFDeriv ℝ k (radialSquash B : E → E) x‖ ≤ C * B ^ (1 - (k : ℤ)) := by
  obtain ⟨G, hG, hgate⟩ := gate_derivative_bound k hk
  obtain ⟨S, hS, hsat⟩ : ∃ S : ℝ, 0 < S ∧
      (2 ≤ k → ∀ K x : ℝ, |iteratedDeriv k (saturation K) x| ≤ S) := by
    by_cases htwo : 2 ≤ k
    · obtain ⟨S, hS, hs⟩ := saturation_derivative_bound k htwo
      exact ⟨S, hS, fun _ => hs⟩
    · exact ⟨1, zero_lt_one, fun h => (htwo h).elim⟩
  have hR := radialDerivativeConstant_pos k
  refine ⟨G + S + radialDerivativeConstant k, by positivity,
    (fun x => (hgate x).trans (by linarith)),
    (fun htwo K x => (hsat htwo K x).trans (by linarith)), ?_⟩
  intro E _ _ B hB x
  exact (radialSquash_derivative_bound k hB x).trans
    (mul_le_mul_of_nonneg_right (by linarith) (by positivity))

/-- The source's smooth-primitives lemma, witnessed by the explicitly
constructed gate, saturation, and radial squash. Smoothness and bounds are
proved here for all finite orders, including the four orders in the source.
Derivative constants precede the space, hence do not depend on dimension. -/
theorem smooth_primitives :
    ((∀ n : ℕ, ContDiff ℝ n gate) ∧ Monotone gate ∧
      (∀ x : ℝ, 0 ≤ gate x ∧ gate x ≤ 1 ∧ 0 ≤ deriv gate x) ∧
      (∀ x : ℝ, x ≤ 1 / 4 → gate x = 0) ∧
      (∀ x : ℝ, 1 / 2 ≤ x → gate x = 1) ∧
      tsupport (deriv gate) ⊆ Ioo (1 / 4 : ℝ) (1 / 2)) ∧
    (∀ K : ℝ, 1 ≤ K → (∀ n : ℕ, ContDiff ℝ n (saturation K)) ∧
      (∀ x : ℝ, |x| ≤ K → saturation K x = x) ∧
      (∀ x : ℝ, |saturation K x| ≤ K + 1) ∧
      (∀ x : ℝ, |deriv (saturation K) x| ≤ 1)) ∧
    (∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E],
      ∀ B : ℝ, 0 < B → (∀ n : ℕ, ContDiff ℝ n (radialSquash B : E → E)) ∧
      (∀ x : E, radialSquash B x = radialCutoff ((‖x‖ / B) ^ 2) • x) ∧
      (∀ x : E, ‖x‖ ≤ B → radialSquash B x = x) ∧
      (∀ x : E, ‖radialSquash B x‖ ≤ 2 * B)) ∧
    (∀ k : ℕ, 1 ≤ k → ∃ C : ℝ, 0 < C ∧
      (∀ x : ℝ, |iteratedDeriv k gate x| ≤ C) ∧
      (2 ≤ k → ∀ K x : ℝ, |iteratedDeriv k (saturation K) x| ≤ C) ∧
      ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E],
        ∀ B : ℝ, 0 < B → ∀ x : E,
          ‖iteratedFDeriv ℝ k (radialSquash B : E → E) x‖ ≤ C * B ^ (1 - (k : ℤ))) := by
  refine ⟨⟨gate_contDiff, gate_monotone, ?_, ?_, ?_, gate_deriv_tsupport⟩,
    ?_, ?_, smooth_primitive_derivative_bounds⟩
  · intro x
    exact ⟨gate_nonneg x, gate_le_one x, gate_deriv_nonneg x⟩
  · intro x hx
    exact gate_zero_of_le (by linarith)
  · intro x hx
    exact gate_one_of_le (by linarith)
  · intro K hK
    have hK0 : 0 ≤ K := by linarith
    exact ⟨saturation_contDiff K, fun _ hx => saturation_eq_self hK0 hx,
      saturation_bound hK0, saturation_deriv_bound hK0⟩
  · intro E _ _ B hB
    exact ⟨radialSquash_contDiff B, radialSquash_radial hB,
      fun _ hx => radialSquash_eq_self hB hx, radialSquash_norm_le hB⟩

end RandomizedFO2003.Primitives
