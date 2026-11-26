import RandomizedFO2003.TensorOverlap
import RandomizedFO2003.DerivativeComposition

namespace RandomizedFO2003.Cascade

open scoped BigOperators

variable {I X Y : Type*} [Fintype I] [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem iteratedFDeriv_sum_comp_linear (n : ℕ) (P : I → X →L[ℝ] Y)
    (f : I → Y → ℝ) (hf : ∀ i, ContDiff ℝ n (f i)) (x : X) :
    iteratedFDeriv ℝ n (fun y => ∑ i, f i (P i y)) x =
      tensorSum n P (fun i => iteratedFDeriv ℝ n (f i) (P i x)) := by
  have h := iteratedFDeriv_sum (fun i (_hi : i ∈ (Finset.univ : Finset I)) =>
    (hf i).comp (P i).contDiff)
  calc
    _ = ∑ i, iteratedFDeriv ℝ n (f i ∘ P i) x := by
      simpa only [Function.comp_apply, Finset.sum_apply] using congrArg (fun q => q x) h
    _ = _ := by
      unfold tensorSum
      apply Finset.sum_congr rfl
      intro i _hi
      exact (P i).iteratedFDeriv_comp_right (hf i) x le_rfl

theorem local_sum_second_derivative_bound (P : I → X →L[ℝ] Y)
    (f : I → Y → ℝ) (hf : ∀ i, ContDiff ℝ 2 (f i)) {C M : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (henergy : ∀ x, ∑ i, ‖P i x‖ ^ 2 ≤ C * ‖x‖ ^ 2) (x : X)
    (hb : ∀ i, ‖iteratedFDeriv ℝ 2 (f i) (P i x)‖ ≤ M) :
    ‖iteratedFDeriv ℝ 2 (fun y => ∑ i, f i (P i y)) x‖ ≤ C * M := by
  rw [iteratedFDeriv_sum_comp_linear 2 P f hf x]
  exact tensorSum_two_norm_le P _ hC hM henergy hb

theorem local_sum_third_derivative_bound (P : I → X →L[ℝ] Y)
    (f : I → Y → ℝ) (hf : ∀ i, ContDiff ℝ 3 (f i)) {C M : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (henergy : ∀ x, ∑ i, ‖P i x‖ ^ 2 ≤ C * ‖x‖ ^ 2)
    (hcontract : ∀ i x, ‖P i x‖ ≤ ‖x‖) (x : X)
    (hb : ∀ i, ‖iteratedFDeriv ℝ 3 (f i) (P i x)‖ ≤ M) :
    ‖iteratedFDeriv ℝ 3 (fun y => ∑ i, f i (P i y)) x‖ ≤ C * M := by
  rw [iteratedFDeriv_sum_comp_linear 3 P f hf x]
  exact tensorSum_three_norm_le P _ hC hM henergy hcontract hb

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem block_sum_second_derivative_bound {N : ℕ} (f : Fin N → E → ℝ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) {M : ℝ} (hM : 0 ≤ M) (x : BlockProduct N E)
    (hb : ∀ i, ‖iteratedFDeriv ℝ 2 (f i) (x i)‖ ≤ M) :
    ‖iteratedFDeriv ℝ 2 (fun y : BlockProduct N E => ∑ i, f i (y i)) x‖ ≤ M := by
  simpa only [one_mul] using local_sum_second_derivative_bound (blockProjection (E := E) N) f hf
    (C := 1) zero_le_one hM (fun y : BlockProduct N E => by
      simpa only [blockProjection_apply, one_mul] using (block_energy_sum y).le) x hb

theorem block_sum_third_derivative_bound {N : ℕ} (f : Fin N → E → ℝ)
    (hf : ∀ i, ContDiff ℝ 3 (f i)) {M : ℝ} (hM : 0 ≤ M) (x : BlockProduct N E)
    (hb : ∀ i, ‖iteratedFDeriv ℝ 3 (f i) (x i)‖ ≤ M) :
    ‖iteratedFDeriv ℝ 3 (fun y : BlockProduct N E => ∑ i, f i (y i)) x‖ ≤ M := by
  simpa only [one_mul] using local_sum_third_derivative_bound (blockProjection (E := E) N) f hf
    (C := 1) zero_le_one hM (fun y : BlockProduct N E => by
      simpa only [blockProjection_apply, one_mul] using (block_energy_sum y).le)
    (fun i y => block_norm_le y i) x hb

theorem edge_sum_second_derivative_bound {N : ℕ} (f : Fin N → E × E → ℝ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) {M : ℝ} (hM : 0 ≤ M) (x : BlockProduct (N + 1) E)
    (hb : ∀ j, ‖iteratedFDeriv ℝ 2 (f j) (x j.castSucc, x j.succ)‖ ≤ M) :
    ‖iteratedFDeriv ℝ 2 (fun y : BlockProduct (N + 1) E => ∑ j, f j (y j.castSucc, y j.succ)) x‖ ≤
      2 * M :=
  local_sum_second_derivative_bound (edgeProjection (E := E) N) f hf (by norm_num) hM edge_energy_sum_le x hb

theorem edge_sum_third_derivative_bound {N : ℕ} (f : Fin N → E × E → ℝ)
    (hf : ∀ i, ContDiff ℝ 3 (f i)) {M : ℝ} (hM : 0 ≤ M) (x : BlockProduct (N + 1) E)
    (hb : ∀ j, ‖iteratedFDeriv ℝ 3 (f j) (x j.castSucc, x j.succ)‖ ≤ M) :
    ‖iteratedFDeriv ℝ 3 (fun y : BlockProduct (N + 1) E => ∑ j, f j (y j.castSucc, y j.succ)) x‖ ≤
      2 * M :=
  local_sum_third_derivative_bound (edgeProjection (E := E) N) f hf (by norm_num) hM edge_energy_sum_le
    edgeProjection_apply_norm_le x hb

end RandomizedFO2003.Cascade
