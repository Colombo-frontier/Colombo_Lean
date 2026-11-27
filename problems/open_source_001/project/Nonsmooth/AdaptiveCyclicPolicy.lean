import Nonsmooth.AdaptiveBlockLegality
import Nonsmooth.PeakValueMonotonicity
import Nonsmooth.DimensionCircularPrecision

open MeasureTheory
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem adaptive_cyclic_controller_step {C X : Type} (N : ℕ)
    (q : C → ℤ → X) (next : C → ℤ → C) (out : C → X)
    (hperiodic : ∀ c, Function.Periodic (q c) (4 * 2 ^ N))
    (hanchor : ∀ c, q c 0 = out c) (hnext : ∀ c j, out (next c j) = q c j)
    (f : X → ℝ) (c0 : C) (m : ℕ) :
    let c := adaptiveBlockController (cyclicPeakPolicy N) (3 * N + 4) q next f c0 m
    let c' := adaptiveBlockController (cyclicPeakPolicy N) (3 * N + 4) q next f c0 (m + 1)
    ∃ j : ℤ, c' = next c j ∧ out c' = q c j ∧ f (out c) ≤ f (out c') ∧
      f (q c (j - 1)) ≤ f (out c') ∧ f (q c (j + 1)) ≤ f (out c') := by
  dsimp only
  let c := adaptiveBlockController (cyclicPeakPolicy N) (3 * N + 4) q next f c0 m
  let j := (cyclicPeakPolicy N).result (fun i => f (q c i)) () (3 * N + 4)
  have hl := cyclicPeakPolicy_local_max N (fun i => f (q c i)) (fun i => congrArg f (hperiodic c i))
  have hzero := cyclicPeakPolicy_value_ge_zero (fun i => f (q c i)) N
  refine ⟨j, rfl, hnext c j, ?_, ?_, ?_⟩
  · change f (out c) ≤ f (out (next c j))
    rw [hnext, ← hanchor]
    exact hzero
  · change f (q c (j - 1)) ≤ f (out (next c j))
    rw [hnext]
    exact hl.1
  · change f (q c (j + 1)) ≤ f (out (next c j))
    rw [hnext]
    exact hl.2

theorem adaptive_cyclic_controller_value_monotone {C X : Type} (N : ℕ)
    (q : C → ℤ → X) (next : C → ℤ → C) (out : C → X)
    (hperiodic : ∀ c, Function.Periodic (q c) (4 * 2 ^ N))
    (hanchor : ∀ c, q c 0 = out c) (hnext : ∀ c j, out (next c j) = q c j)
    (f : X → ℝ) (c0 : C) :
    Monotone (fun m => f (out (adaptiveBlockController (cyclicPeakPolicy N) (3 * N + 4) q next f c0 m))) := by
  apply monotone_nat_of_le_succ
  intro m
  obtain ⟨j, _, _, hval, _, _⟩ := adaptive_cyclic_controller_step N q next out hperiodic hanchor hnext f c0 m
  exact hval

theorem adaptive_cyclic_policy_legal_monotone {C X : Type}
    [MeasurableSpace C] [Countable C] [MeasurableSingletonClass C] [StandardBorelSpace C]
    [MeasurableSpace X] (N : ℕ) (q : C → ℤ → X) (next : C → ℤ → C) (out : C → X)
    (hperiodic : ∀ c, Function.Periodic (q c) (4 * 2 ^ N))
    (hanchor : ∀ c, q c 0 = out c) (hnext : ∀ c j, out (next c j) = q c j) (c0 : C) :
    ∃ p : Policy Unit (C × CyclicPeakState) X, p.IsMeasurable ∧
      ∀ f : X → ℝ,
        (∀ m, p.result f () (m * (3 * N + 4)) =
          out (adaptiveBlockController (cyclicPeakPolicy N) (3 * N + 4) q next f c0 m)) ∧
        Monotone (fun m => f (p.result f () (m * (3 * N + 4)))) := by
  let p := adaptiveBlockPolicy (cyclicPeakPolicy N) (3 * N + 4) q next out c0
  refine ⟨p, adaptiveBlockPolicy_measurable _ (cyclicPeakPolicy_measurable N) _ q next out c0, ?_⟩
  intro f
  have hres (m : ℕ) : p.result f () (m * (3 * N + 4)) =
      out (adaptiveBlockController (cyclicPeakPolicy N) (3 * N + 4) q next f c0 m) :=
    adaptiveBlockPolicy_result_exact _ (by omega) q next out c0 f m
  refine ⟨hres, ?_⟩
  simpa only [hres] using adaptive_cyclic_controller_value_monotone N q next out hperiodic hanchor hnext f c0

theorem adaptive_cyclic_dimension_query_bound (D : ℕ) (hD : 0 < D) (m : ℕ) (hm : m ≤ D) :
    ((m * (3 * dimensionCircularPrecision D + 4) : ℕ) : ℝ) ≤
      62 * (D : ℝ) * Real.log ((D : ℝ) + 1) := by
  have hs := dimensionCircularPrecision_query_bound D hD
  have hcast : (m : ℝ) ≤ D := by exact_mod_cast hm
  have hT : (0 : ℝ) ≤ (3 * dimensionCircularPrecision D + 4 : ℕ) := Nat.cast_nonneg _
  have h1 := mul_le_mul_of_nonneg_right hcast hT
  have h2 := mul_le_mul_of_nonneg_left hs (show (0 : ℝ) ≤ D from Nat.cast_nonneg D)
  push_cast at h1 h2 ⊢
  nlinarith only [h1, h2]

end
end Nonsmooth
