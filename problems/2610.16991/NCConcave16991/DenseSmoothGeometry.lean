import NCConcave16991.DenseSmoothLocal

/-! # Actual neighboring-block projections of the dense radial chain -/

noncomputable section

namespace NCConcave16991.DenseSmooth

open ConeSmooth
open scoped BigOperators InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] {T : ℕ}

def previousProjection (j : Fin (T + 1)) : Blocks E T →L[ℝ] E :=
  if h : j.val = 0 then 0 else blockProjection ⟨j.val - 1, by omega⟩

def stageProjection (j : Fin (T + 1)) : Blocks E T →L[ℝ] Pair E :=
  pairMap (previousProjection j) (blockProjection j)

def previousDirection (u : Fin (T + 1) → E) (j : Fin (T + 1)) : E :=
  if h : j.val = 0 then u 0 else u ⟨j.val - 1, by omega⟩

theorem previousDirection_unit (u : Fin (T + 1) → E) (hu : ∀ j, ‖u j‖ = 1) (j : Fin (T + 1)) :
    ‖previousDirection u j‖ = 1 := by unfold previousDirection; split <;> exact hu _

theorem previousProjection_energy (x : Blocks E T) :
    (∑ j, ‖previousProjection j x‖ ^ 2) ≤ ‖x‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  calc
    (∑ j, ‖previousProjection j x‖ ^ 2) = ∑ i : Fin T, ‖x i.castSucc‖ ^ 2 := by
      rw [Fin.sum_univ_succ]
      simp only [previousProjection, Fin.val_zero, ↓reduceDIte, zero_apply, norm_zero,
        zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add, Fin.val_succ,
        Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceDIte, Nat.add_sub_cancel]
      apply Finset.sum_congr rfl
      intro j hj
      rfl
    _ ≤ ∑ j : Fin (T + 1), ‖x j‖ ^ 2 := by
      rw [Fin.sum_univ_castSucc]
      linarith [sq_nonneg ‖x (Fin.last T)‖]

theorem stageProjection_energy (x : Blocks E T) :
    (∑ j, ‖stageProjection j x‖ ^ 2) ≤ 2 * ‖x‖ ^ 2 := by
  have he (j : Fin (T + 1)) : ‖stageProjection j x‖ ^ 2 = ‖previousProjection j x‖ ^ 2 + ‖x j‖ ^ 2 := by
    rw [stageProjection, pairMap_apply, WithLp.prod_norm_sq_eq_of_L2]
    rfl
  simp only [he, Finset.sum_add_distrib]
  rw [← PiLp.norm_sq_eq_of_L2]
  have hh := previousProjection_energy x
  linarith

theorem componentChain_eq_stages {n : ℕ} (ρ : ℝ) (u : Fin (T + 1) → E)
    (rows : Fin n → Fin (T + 1) → E) (i : Fin n) :
    componentChain ρ u rows i = fun x ↦
      (∑ j, localCore (decide (j.val = 0)) ρ (previousDirection u j) (rows i j) (stageProjection j x)) +
        (33 / 32 : ℝ) * ‖x‖ ^ 2 := by
  funext x
  rw [Fin.sum_univ_succ]
  simp only [localCore, Fin.val_zero, decide_true, ↓reduceIte, Fin.val_succ,
    Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, decide_false]
  change componentChain ρ u rows i x = -scaledRadialCoordinate ρ (rows i 0) (x 0) +
    (∑ j : Fin T, -(gate (radialCoordinate (previousDirection u j.succ)
      (previousProjection j.succ x)) * (scaledRadialCoordinate ρ (rows i j.succ) (x j.succ) + 1))) + _
  have hprev (j : Fin T) : previousProjection (E := E) j.succ x = x j.castSucc := by
    unfold previousProjection
    simp only [Fin.val_succ, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceDIte,
      Nat.add_sub_cancel]
    rfl
  have hdir (j : Fin T) : previousDirection u j.succ = u j.castSucc := by
    unfold previousDirection
    simp only [Fin.val_succ, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceDIte,
      Nat.add_sub_cancel]
    rfl
  simp only [hprev, hdir, Finset.sum_neg_distrib, componentChain, coordinate]
  ring

end NCConcave16991.DenseSmooth
