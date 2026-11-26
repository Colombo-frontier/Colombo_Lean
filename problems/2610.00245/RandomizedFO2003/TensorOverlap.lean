import RandomizedFO2003.BlockEnergy
import Mathlib.Analysis.NormedSpace.Multilinear.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

namespace RandomizedFO2003.Cascade

open scoped BigOperators

variable {I X Y : Type*} [Fintype I] [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem projection_norm_products_le (P : I → X →L[ℝ] Y) {C : ℝ} (hC : 0 ≤ C)
    (henergy : ∀ x, ∑ i, ‖P i x‖ ^ 2 ≤ C * ‖x‖ ^ 2) (x y : X) :
    ∑ i, ‖P i x‖ * ‖P i y‖ ≤ C * ‖x‖ * ‖y‖ := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖P i x‖) (fun i => ‖P i y‖)
  have hmul : (∑ i, ‖P i x‖ ^ 2) * ∑ i, ‖P i y‖ ^ 2 ≤
      (C * ‖x‖ ^ 2) * (C * ‖y‖ ^ 2) :=
    mul_le_mul (henergy x) (henergy y) (Finset.sum_nonneg (fun i _ => sq_nonneg _)) (by positivity)
  apply (sq_le_sq₀ (Finset.sum_nonneg (fun i _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    (by positivity : 0 ≤ C * ‖x‖ * ‖y‖)).mp
  exact (hcs.trans hmul).trans_eq (by ring)

theorem projection_norm_triples_le (P : I → X →L[ℝ] Y) {C : ℝ} (hC : 0 ≤ C)
    (henergy : ∀ x, ∑ i, ‖P i x‖ ^ 2 ≤ C * ‖x‖ ^ 2)
    (hcontract : ∀ i x, ‖P i x‖ ≤ ‖x‖) (x y z : X) :
    ∑ i, ‖P i x‖ * ‖P i y‖ * ‖P i z‖ ≤ C * ‖x‖ * ‖y‖ * ‖z‖ := by
  calc
    _ ≤ ∑ i, ‖P i x‖ * ‖P i y‖ * ‖z‖ :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hcontract i z) (by positivity))
    _ = (∑ i, ‖P i x‖ * ‖P i y‖) * ‖z‖ := (Finset.sum_mul ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (projection_norm_products_le P hC henergy x y) (norm_nonneg z)

noncomputable def tensorSum (n : ℕ) (P : I → X →L[ℝ] Y)
    (T : I → ContinuousMultilinearMap ℝ (fun _ : Fin n => Y) ℝ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin n => X) ℝ :=
  ∑ i, (T i).compContinuousLinearMap (fun _ => P i)

@[simp] theorem tensorSum_apply (n : ℕ) (P : I → X →L[ℝ] Y)
    (T : I → ContinuousMultilinearMap ℝ (fun _ : Fin n => Y) ℝ) (v : Fin n → X) :
    tensorSum n P T v = ∑ i, T i (fun j => P i (v j)) := by
  simp [tensorSum, ContinuousMultilinearMap.compContinuousLinearMap_apply]

/-- A family of bilinear tensors with bounded projection energy can be
summed without a factor equal to the number of tensors. -/
theorem tensorSum_two_norm_le (P : I → X →L[ℝ] Y)
    (T : I → ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Y) ℝ)
    {C M : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (henergy : ∀ x, ∑ i, ‖P i x‖ ^ 2 ≤ C * ‖x‖ ^ 2) (hT : ∀ i, ‖T i‖ ≤ M) :
    ‖tensorSum 2 P T‖ ≤ C * M := by
  apply ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg hC hM)
  intro v
  rw [tensorSum_apply, Fin.prod_univ_two]
  calc
    _ ≤ ∑ i, ‖T i (fun j => P i (v j))‖ := norm_sum_le _ _
    _ ≤ ∑ i, M * (‖P i (v 0)‖ * ‖P i (v 1)‖) := by
      apply Finset.sum_le_sum
      intro i _hi
      apply (T i).le_opNorm (fun j => P i (v j)) |>.trans
      rw [Fin.prod_univ_two]
      exact mul_le_mul_of_nonneg_right (hT i) (by positivity)
    _ = M * ∑ i, ‖P i (v 0)‖ * ‖P i (v 1)‖ := (Finset.mul_sum ..).symm
    _ ≤ M * (C * ‖v 0‖ * ‖v 1‖) :=
      mul_le_mul_of_nonneg_left (projection_norm_products_le P hC henergy (v 0) (v 1)) hM
    _ = _ := by ring

/-- The third-order analogue uses one contraction bound in addition to the
same quadratic projection-energy estimate. -/
theorem tensorSum_three_norm_le (P : I → X →L[ℝ] Y)
    (T : I → ContinuousMultilinearMap ℝ (fun _ : Fin 3 => Y) ℝ)
    {C M : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (henergy : ∀ x, ∑ i, ‖P i x‖ ^ 2 ≤ C * ‖x‖ ^ 2)
    (hcontract : ∀ i x, ‖P i x‖ ≤ ‖x‖) (hT : ∀ i, ‖T i‖ ≤ M) :
    ‖tensorSum 3 P T‖ ≤ C * M := by
  apply ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg hC hM)
  intro v
  rw [tensorSum_apply, Fin.prod_univ_three]
  calc
    _ ≤ ∑ i, ‖T i (fun j => P i (v j))‖ := norm_sum_le _ _
    _ ≤ ∑ i, M * (‖P i (v 0)‖ * ‖P i (v 1)‖ * ‖P i (v 2)‖) := by
      apply Finset.sum_le_sum
      intro i _hi
      apply (T i).le_opNorm (fun j => P i (v j)) |>.trans
      rw [Fin.prod_univ_three]
      exact mul_le_mul_of_nonneg_right (hT i) (by positivity)
    _ = M * ∑ i, ‖P i (v 0)‖ * ‖P i (v 1)‖ * ‖P i (v 2)‖ := (Finset.mul_sum ..).symm
    _ ≤ M * (C * ‖v 0‖ * ‖v 1‖ * ‖v 2‖) :=
      mul_le_mul_of_nonneg_left
        (projection_norm_triples_le P hC henergy hcontract (v 0) (v 1) (v 2)) hM
    _ = _ := by ring

end RandomizedFO2003.Cascade
