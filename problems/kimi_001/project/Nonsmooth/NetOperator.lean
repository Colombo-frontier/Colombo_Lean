import Nonsmooth.SphereNet
import Nonsmooth.SupportGram

open MeasureTheory Function
open scoped InnerProductSpace Topology
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section

theorem linear_net_lower_bound {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (A : V →L[ℝ] E) (s : Finset V)
    (hnet : ∀ x : V, ‖x‖ = 1 → ∃ y ∈ s, ‖x - y‖ ≤ 1 / 16)
    {r : ℝ} (hr : 0 ≤ r)
    (hs : ∀ y ∈ s, r ^ 2 / 2 ≤ ‖A y‖ ^ 2 ∧ ‖A y‖ ^ 2 ≤ 2 * r ^ 2) :
    ∀ x : V, (r / 2) * ‖x‖ ≤ ‖A x‖ := by
  have hu (y : V) (hy : y ∈ s) : ‖A y‖ ≤ (3 / 2) * r := by
    have h := (hs y hy).2
    nlinarith [norm_nonneg (A y), sq_nonneg (‖A y‖ - (3 / 2) * r)]
  have hl (y : V) (hy : y ∈ s) : (5 / 8) * r ≤ ‖A y‖ := by
    have h := (hs y hy).1
    nlinarith [norm_nonneg (A y), sq_nonneg (‖A y‖ - (5 / 8) * r)]
  have hop : ‖A‖ ≤ (3 / 2) * r + ‖A‖ / 16 := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hnet x hx
    have hd := (A.le_opNorm (x - y)).trans
      (mul_le_mul_of_nonneg_left hxy (norm_nonneg A))
    have ht : ‖A x‖ ≤ ‖A y‖ + ‖A (x - y)‖ := by
      rw [map_sub]
      exact norm_le_insert' _ _
    have hyu := hu y hy
    linarith
  have hop' : ‖A‖ ≤ 2 * r := by linarith
  have hunit (x : V) (hx : ‖x‖ = 1) : r / 2 ≤ ‖A x‖ := by
    obtain ⟨y, hy, hxy⟩ := hnet x hx
    have hd := (A.le_opNorm (x - y)).trans
      (mul_le_mul_of_nonneg_left hxy (norm_nonneg A))
    have ht : ‖A y‖ ≤ ‖A x‖ + ‖A (x - y)‖ := by
      rw [map_sub, norm_sub_rev]
      exact norm_le_insert' _ _
    have hyl := hl y hy
    linarith
  intro x
  by_cases hx : x = 0
  · simp [hx]
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hxn : ‖‖x‖⁻¹ • x‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  have h := hunit (‖x‖⁻¹ • x) hxn
  rw [map_smul, norm_smul, norm_inv, norm_norm, ← div_eq_inv_mul] at h
  exact (le_div_iff₀ hn).mp h

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

def supportEuclideanSynthesis {k : ℕ} (a : Fin k → E) : EuclideanSpace ℝ (Fin k) →L[ℝ] E :=
  ((supportRowSynthesis a).comp (WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).toLinearMap).toContinuousLinearMap

theorem supportEuclideanSynthesis_apply {k : ℕ} (a : Fin k → E) (c : EuclideanSpace ℝ (Fin k)) :
    supportEuclideanSynthesis a c = supportRowSynthesis a (fun i => c i) := rfl

theorem euclidean_coeff_norm_square {k : ℕ} (c : EuclideanSpace ℝ (Fin k)) :
    ‖c‖ ^ 2 = ∑ i, (c i) ^ 2 := by
  simpa only [Real.norm_eq_abs, sq_abs] using PiLp.norm_sq_eq_of_L2 (fun _ : Fin k => ℝ) c

theorem support_synthesis_lower_of_net {k : ℕ} (a : Fin k → E)
    (s : Finset (EuclideanSpace ℝ (Fin k)))
    (hnet : ∀ x : EuclideanSpace ℝ (Fin k), ‖x‖ = 1 → ∃ y ∈ s, ‖x - y‖ ≤ 1 / 16)
    {r : ℝ} (hr : 0 ≤ r)
    (hs : ∀ c ∈ s, r ^ 2 / 2 ≤ ‖supportRowSynthesis a (fun i => c i)‖ ^ 2 ∧
      ‖supportRowSynthesis a (fun i => c i)‖ ^ 2 ≤ 2 * r ^ 2) :
    ∀ c : Fin k → ℝ, (r ^ 2 / 4) * (∑ i, (c i) ^ 2) ≤ ‖supportRowSynthesis a c‖ ^ 2 := by
  intro c
  let v : EuclideanSpace ℝ (Fin k) := (WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).symm c
  have h := linear_net_lower_bound (supportEuclideanSynthesis a) s hnet hr hs v
  have he : ‖v‖ ^ 2 = ∑ i, (c i) ^ 2 := euclidean_coeff_norm_square v
  change (r / 2) * ‖v‖ ≤ ‖supportRowSynthesis a c‖ at h
  have hsquare := mul_self_le_mul_self (by positivity : 0 ≤ (r / 2) * ‖v‖) h
  nlinarith [he]

end
end Nonsmooth
