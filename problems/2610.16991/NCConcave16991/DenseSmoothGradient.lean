import NCConcave16991.DenseSmoothConstruction
import Mathlib.Analysis.Calculus.Gradient.Basic

/-! # Actual full primal gradient and the first unfinished-stage barrier -/

noncomputable section

namespace NCConcave16991.DenseSmooth

open Set
open scoped BigOperators InnerProductSpace

set_option maxHeartbeats 800000
set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 4

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] {T : ℕ}

def coordinateDerivative (u : Fin (T + 1) → E) (x : Blocks E T) (j : Fin (T + 1)) : Blocks E T →L[ℝ] ℝ :=
  (innerSL ℝ (radialCoordinateGradient (u j) (x j))).comp (blockProjection j)

theorem coordinate_hasFDerivAt (u : Fin (T + 1) → E) (x : Blocks E T) (j : Fin (T + 1)) :
    HasFDerivAt (fun z : Blocks E T ↦ coordinate u z j) (coordinateDerivative u x j) x :=
  (hasFDerivAt_radialCoordinate (u j) (x j)).comp x (blockProjection j).hasFDerivAt

def previousGate (u : Fin (T + 1) → E) (x : Blocks E T) (j : Fin (T + 1)) : ℝ :=
  if h : j.val = 0 then 1 else gate (coordinate u x ⟨j.val - 1, by omega⟩)

def nextCoefficient (u : Fin (T + 1) → E) (x : Blocks E T) (j : Fin (T + 1)) : ℝ :=
  if h : j.val < T then gateD (coordinate u x j) * (coordinate u x ⟨j.val + 1, by omega⟩ + 1) else 0

def meanGradient (u : Fin (T + 1) → E) (x : Blocks E T) : Blocks E T :=
  WithLp.toLp 2 (fun j ↦ (33 / 16 : ℝ) • x j -
    (previousGate u x j + nextCoefficient u x j) • radialCoordinateGradient (u j) (x j))

theorem currentDerivative_sum (u : Fin (T + 1) → E) (x : Blocks E T) :
    coordinateDerivative u x 0 + ∑ j : Fin T,
      gate (coordinate u x j.castSucc) • coordinateDerivative u x j.succ =
      ∑ j, previousGate u x j • coordinateDerivative u x j := by
  rw [Fin.sum_univ_succ]
  simp only [previousGate, Fin.val_zero, ↓reduceDIte, one_smul, Fin.val_succ,
    Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceDIte, Nat.add_sub_cancel]
  rfl

theorem nextDerivative_sum (u : Fin (T + 1) → E) (x : Blocks E T) :
    (∑ j : Fin T, (gateD (coordinate u x j.castSucc) * (coordinate u x j.succ + 1)) •
      coordinateDerivative u x j.castSucc) =
      ∑ j, nextCoefficient u x j • coordinateDerivative u x j := by
  rw [Fin.sum_univ_castSucc]
  simp only [nextCoefficient, Fin.val_last, lt_self_iff_false, ↓reduceDIte, zero_smul, add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  rw [dif_pos (by simpa using j.isLt)]
  rfl

theorem meanChain_hasFDerivAt (u : Fin (T + 1) → E) (x : Blocks E T) :
    HasFDerivAt (meanChain u) (innerSL ℝ (meanGradient u x)) x := by
  have hlink (j : Fin T) :
      HasFDerivAt (fun z : Blocks E T ↦ gate (coordinate u z j.castSucc) * (coordinate u z j.succ + 1))
        (gate (coordinate u x j.castSucc) • coordinateDerivative u x j.succ +
          (gateD (coordinate u x j.castSucc) * (coordinate u x j.succ + 1)) • coordinateDerivative u x j.castSucc) x := by
    convert ((gate_hasDerivAt (coordinate u x j.castSucc)).comp_hasFDerivAt x
      (coordinate_hasFDerivAt u x j.castSucc)).mul ((coordinate_hasFDerivAt u x j.succ).add_const 1) using 1 <;> try rfl
    ext h
    simp only [add_apply, smul_apply, smul_eq_mul, Function.comp_apply]
    ring
  have hh := (((coordinate_hasFDerivAt u x 0).neg).sub
    (HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ ↦ hlink j))).add
      (((hasFDerivAt_id x).norm_sq).const_mul (33 / 32 : ℝ))
  change HasFDerivAt (meanChain u) _ x at hh
  refine hh.congr_fderiv ?_
  have hcur := currentDerivative_sum u x
  have hnxt := nextDerivative_sum u x
  ext h
  have hcur' := congrArg (fun L : Blocks E T →L[ℝ] ℝ ↦ L h) hcur
  have hnxt' := congrArg (fun L : Blocks E T →L[ℝ] ℝ ↦ L h) hnxt
  simp only [ContinuousLinearMap.sum_apply, add_apply, smul_apply, smul_eq_mul] at hcur' hnxt'
  simp only [add_apply, sub_apply, ContinuousLinearMap.neg_apply, smul_apply,
    ContinuousLinearMap.sum_apply, smul_eq_mul, innerSL_apply_apply, meanGradient,
    PiLp.inner_apply, inner_sub_left, real_inner_smul_left]
  have hproj (j : Fin (T + 1)) : blockProjection j h = h j := rfl
  simp only [coordinateDerivative, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    innerSL_apply_apply, hproj, Function.comp_apply, id_eq, smul_eq_mul, PiLp.inner_apply,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_add, Finset.mul_sum] at hcur' hnxt' ⊢
  simp only [smul_eq_mul, add_mul, mul_one, Finset.sum_add_distrib, ← Finset.mul_sum] at hcur' hnxt' ⊢
  simp only [two_smul]
  linarith

theorem meanChain_hasGradientAt (u : Fin (T + 1) → E) (x : Blocks E T) :
    HasGradientAt (meanChain u) (meanGradient u x) x := meanChain_hasFDerivAt u x

theorem nextCoefficient_nonneg (u : Fin (T + 1) → E) (hu : ∀ j, ‖u j‖ = 1)
    (x : Blocks E T) (j : Fin (T + 1)) : 0 ≤ nextCoefficient u x j := by
  unfold nextCoefficient
  split_ifs with hnext
  · exact mul_nonneg (gateD_nonneg _) (by
      have hh := abs_radialCoordinate_lt_one (hu ⟨j.val + 1, by omega⟩) (x ⟨j.val + 1, by omega⟩)
      have hh' := (abs_lt.mp hh).1
      change 0 ≤ radialCoordinate (u ⟨j.val + 1, by omega⟩) (x ⟨j.val + 1, by omega⟩) + 1
      exact le_of_lt (by linarith))
  · exact le_rfl

theorem unfinished_gradient_barrier (u : Fin (T + 1) → E) (hu : ∀ j, ‖u j‖ = 1)
    (x : Blocks E T) (hbad : ∃ j, coordinate u x j < 9 / 32) :
    (5 / 18 : ℝ) < ‖gradient (meanChain u) x‖ := by
  let S : Finset (Fin (T + 1)) := Finset.univ.filter (fun j ↦ coordinate u x j < 9 / 32)
  have hS : S.Nonempty := by rcases hbad with ⟨j, hj⟩; exact ⟨j, by simp [S, hj]⟩
  let j := S.min' hS
  have hjS : j ∈ S := Finset.min'_mem S hS
  have hjbad : coordinate u x j < 9 / 32 := (Finset.mem_filter.mp hjS).2
  have hprev : previousGate u x j = 1 := by
    unfold previousGate
    split_ifs with hj0
    · rfl
    · apply gate_one
      by_contra h
      have hbadprev : coordinate u x ⟨j.val - 1, by omega⟩ < 9 / 32 := lt_of_not_ge h
      have hm := Finset.min'_le S ⟨j.val - 1, by omega⟩ (by simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]; exact hbadprev)
      have hv := Fin.le_def.mp hm
      change j.val ≤ j.val - 1 at hv
      omega
  have hc : 1 ≤ previousGate u x j + nextCoefficient u x j := by
    rw [hprev]
    linarith [nextCoefficient_nonneg u hu x j]
  have hh := radialCoordinateGradient_comparison (hu j) (x j) hc hjbad.le
  have hn : ‖meanGradient u x j‖ ≤ ‖meanGradient u x‖ := PiLp.norm_apply_le (p := 2) (meanGradient u x) j
  have hb : (5 / 18 : ℝ) < ‖meanGradient u x j‖ := hh.2.trans_le hh.1
  rw [(meanChain_hasGradientAt u x).gradient]
  exact hb.trans_le hn

end NCConcave16991.DenseSmooth
