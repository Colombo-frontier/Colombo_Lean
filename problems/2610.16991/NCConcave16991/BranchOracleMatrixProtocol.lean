import NCConcave16991.BranchOracleMarking

/-! # Exact physical forward/transpose replies and their public mark slots -/

namespace NCConcave16991.BranchOracle
noncomputable section
open GlobalHard
open scoped InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048
set_option maxSynthPendingDepth 4
set_option maxHeartbeats 800000

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {M m : ℕ}

theorem macroSite_le_total (j : Fin M) : macroSite m j ≤ M * (m + 1) := by
  have hh := Nat.mul_le_mul_right (m + 1) (Nat.succ_le_iff.mpr j.isLt)
  simpa only [macroSite, Nat.succ_mul] using hh

theorem macroDepth_le_total (j : Fin M) (k : Fin ((m + 1) + 1)) : j.val * (m + 1) + k.val ≤ M * (m + 1) := by
  have hh := macroSite_le_total (m := m) j
  have hk : k.val ≤ m + 1 := Nat.le_of_lt_succ k.isLt
  dsimp [macroSite] at hh
  omega

theorem queryMark_dual (j : Fin M) (k : Fin ((m + 1) + 1)) :
    queryMark E M m (j.val * (m + 1) + k.val) (if k.val < m + 1 then 3 else 4) =
      (PiLp.proj 2 (MacroSpaces (ι := ι) E M m j) k).comp (dualProj (MacroSpaces (ι := ι) E M m) j) := by
  by_cases hk : k.val < m + 1
  · let k' : Fin (m + 1) := ⟨k.val, hk⟩
    have hh := queryMark_interiorDual (ι := ι) E M m j k'
    simp only [if_pos hk]
    exact hh
  · have he : k = Fin.last (m + 1) := by apply Fin.ext; have hh := k.isLt; simp only [Fin.val_last]; omega
    subst k
    simpa only [Fin.val_last, lt_self_iff_false, ite_false, macroSite] using queryMark_terminalDual (ι := ι) E M m j

variable (Q : ∀ d : ℕ, FormalLayer (ι := ι) E d ≃ₗᵢ[ℝ] FormalLayer (ι := ι) E d)

theorem macroBranch_forward (j : Fin M) (t : Fin (m + 1)) (i : ι)
    (x : MacroSpaces (ι := ι) E M m j t.castSucc) :
    (macroBranches E Q j t).branch i x =
      Q (j.val * (m + 1) + t.val + 1)
        (prepend E (j.val * (m + 1) + t.val) i ((Q (j.val * (m + 1) + t.val)).symm x)) := rfl

theorem macroBranch_transpose (j : Fin M) (t : Fin (m + 1)) (i : ι)
    (y : MacroSpaces (ι := ι) E M m j t.succ) :
    ((macroBranches E Q j t).branch i).toContinuousLinearMap.adjoint y =
      Q (j.val * (m + 1) + t.val)
        (slice E (j.val * (m + 1) + t.val) i ((Q (j.val * (m + 1) + t.val + 1)).symm y)) := by
  apply ext_inner_left ℝ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_right]
  simp only [LinearIsometry.coe_toContinuousLinearMap]
  rw [macroBranch_forward]
  let A := Q (j.val * (m + 1) + t.val)
  let B := Q (j.val * (m + 1) + t.val + 1)
  have h1 : ⟪B (prepend E (j.val * (m + 1) + t.val) i (A.symm x)), y⟫_ℝ =
      ⟪prepend E (j.val * (m + 1) + t.val) i (A.symm x), B.symm y⟫_ℝ := by
    calc
      _ = ⟪B (prepend E (j.val * (m + 1) + t.val) i (A.symm x)), B (B.symm y)⟫_ℝ := by rw [B.apply_symm_apply]
      _ = _ := B.inner_map_map _ _
  rw [h1, prepend_inner]
  exact (A.inner_map_map (A.symm x) _).symm.trans (by rw [A.apply_symm_apply])

end
end NCConcave16991.BranchOracle
