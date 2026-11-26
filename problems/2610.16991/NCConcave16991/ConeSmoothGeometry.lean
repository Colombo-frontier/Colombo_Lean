import NCConcave16991.ConeSmoothClock
import NCConcave16991.ConeRecoveryBranch

/-! # The actual local cone projections have overlap load two -/

noncomputable section

namespace NCConcave16991.ConeSmooth

open ConeValue ConeRecovery
open scoped BigOperators InnerProductSpace

section PairMaps

variable {V A B : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]

def pairMap (P : V →L[ℝ] A) (Q : V →L[ℝ] B) : V →L[ℝ] WithLp 2 (A × B) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ A B).symm.toContinuousLinearMap.comp (P.prod Q)

theorem pairMap_apply (P : V →L[ℝ] A) (Q : V →L[ℝ] B) (x : V) :
    pairMap P Q x = WithLp.toLp 2 (P x, Q x) := rfl

theorem fstL_norm_le : ‖WithLp.fstL 2 ℝ A B‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num : (0 : ℝ) ≤ 1)
  intro x
  exact (WithLp.norm_fst_le (p := 2) (α := A) (β := B) x).trans_eq (one_mul _).symm

theorem sndL_norm_le : ‖WithLp.sndL 2 ℝ A B‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num : (0 : ℝ) ≤ 1)
  intro x
  exact (WithLp.norm_snd_le (p := 2) (α := A) (β := B) x).trans_eq (one_mul _).symm

end PairMaps

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {M : ℕ}

abbrev StageSpace (E : Type*) := Pair (Pair E)

def stagePair : StageSpace E →L[ℝ] Pair E := WithLp.fstL 2 ℝ (Pair E) (Pair E)
def stageOther : StageSpace E →L[ℝ] Pair E := WithLp.sndL 2 ℝ (Pair E) (Pair E)
def stageZ : StageSpace E →L[ℝ] E := (pairZ (E := E)).comp stagePair
def stageU : StageSpace E →L[ℝ] E := (pairU (E := E)).comp stagePair
def stagePrevious : StageSpace E →L[ℝ] E := (pairZ (E := E)).comp stageOther
def stageY : StageSpace E →L[ℝ] E := (pairU (E := E)).comp stageOther

theorem stagePair_norm : ‖stagePair (E := E)‖ ≤ 1 := fstL_norm_le
theorem stageOther_norm : ‖stageOther (E := E)‖ ≤ 1 := sndL_norm_le
theorem stageZ_norm : ‖stageZ (E := E)‖ ≤ 1 :=
  ((pairZ (E := E)).opNorm_comp_le stagePair).trans
    ((mul_le_mul pairZ_norm stagePair_norm (norm_nonneg (stagePair (E := E))) (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (by ring))
theorem stageU_norm : ‖stageU (E := E)‖ ≤ 1 :=
  ((pairU (E := E)).opNorm_comp_le stagePair).trans
    ((mul_le_mul pairU_norm stagePair_norm (norm_nonneg (stagePair (E := E))) (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (by ring))
theorem stagePrevious_norm : ‖stagePrevious (E := E)‖ ≤ 1 :=
  ((pairZ (E := E)).opNorm_comp_le stageOther).trans
    ((mul_le_mul pairZ_norm stageOther_norm (norm_nonneg (stageOther (E := E))) (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (by ring))
theorem stageY_norm : ‖stageY (E := E)‖ ≤ 1 :=
  ((pairU (E := E)).opNorm_comp_le stageOther).trans
    ((mul_le_mul pairU_norm stageOther_norm (norm_nonneg (stageOther (E := E))) (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (by ring))

def jointZ (j : Fin (M + 1)) : JointBlocks E M →L[ℝ] E :=
  (zProjection j).comp (WithLp.fstL 2 ℝ (PrimalBlocks E M) (Blocks E M))
def jointU (j : Fin (M + 1)) : JointBlocks E M →L[ℝ] E :=
  (uProjection j).comp (WithLp.fstL 2 ℝ (PrimalBlocks E M) (Blocks E M))
def jointY (j : Fin (M + 1)) : JointBlocks E M →L[ℝ] E :=
  (PiLp.proj 2 (fun _ : Fin (M + 1) ↦ E) j).comp (WithLp.sndL 2 ℝ (PrimalBlocks E M) (Blocks E M))
def jointPrevious (j : Fin (M + 1)) : JointBlocks E M →L[ℝ] E :=
  if h : j.val = 0 then 0 else jointU ⟨j.val - 1, by omega⟩

def stageProjection (j : Fin (M + 1)) : JointBlocks E M →L[ℝ] StageSpace E :=
  pairMap (pairMap (jointZ j) (jointU j)) (pairMap (jointPrevious j) (jointY j))

theorem stageProjection_norm_sq (j : Fin (M + 1)) (x : JointBlocks E M) :
    ‖stageProjection j x‖ ^ 2 = ‖x.fst.fst j‖ ^ 2 + ‖x.fst.snd j‖ ^ 2 +
      ‖jointPrevious j x‖ ^ 2 + ‖x.snd j‖ ^ 2 := by
  rw [stageProjection, pairMap_apply, WithLp.prod_norm_sq_eq_of_L2,
    pairMap_apply, pairMap_apply, WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
  change (‖x.fst.fst j‖ ^ 2 + ‖x.fst.snd j‖ ^ 2) +
    (‖jointPrevious j x‖ ^ 2 + ‖x.snd j‖ ^ 2) = _
  ring

theorem jointPrevious_energy_bound (x : JointBlocks E M) :
    (∑ j, ‖jointPrevious j x‖ ^ 2) ≤ ‖x.fst.snd‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  calc
    (∑ j, ‖jointPrevious j x‖ ^ 2) = ∑ i : Fin M, ‖x.fst.snd i.castSucc‖ ^ 2 := by
      rw [Fin.sum_univ_succ]
      simp only [jointPrevious, Fin.val_zero, ↓reduceDIte, zero_apply, norm_zero,
        zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add, Fin.val_succ,
        Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceDIte, Nat.add_sub_cancel]
      apply Finset.sum_congr rfl
      intro j hj
      rfl
    _ ≤ ∑ j : Fin (M + 1), ‖x.fst.snd j‖ ^ 2 := by
      rw [Fin.sum_univ_castSucc]
      linarith [sq_nonneg ‖x.fst.snd (Fin.last M)‖]

theorem stageProjection_energy_bound (x : JointBlocks E M) :
    (∑ j, ‖stageProjection j x‖ ^ 2) ≤ 2 * ‖x‖ ^ 2 := by
  simp only [stageProjection_norm_sq, Finset.sum_add_distrib]
  rw [← PiLp.norm_sq_eq_of_L2, ← PiLp.norm_sq_eq_of_L2, ← PiLp.norm_sq_eq_of_L2]
  have hp := jointPrevious_energy_bound x
  have hn := WithLp.prod_norm_sq_eq_of_L2 x
  have hx := WithLp.prod_norm_sq_eq_of_L2 x.fst
  nlinarith [sq_nonneg ‖x.fst.fst‖, sq_nonneg ‖x.snd‖]

end NCConcave16991.ConeSmooth
