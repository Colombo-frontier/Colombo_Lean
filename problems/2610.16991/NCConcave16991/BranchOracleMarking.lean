import NCConcave16991.BranchOracleFlat
import NCConcave16991.GlobalHardOutputRecovery

/-! # Five public query marks per depth cover every actual coordinate block -/

namespace NCConcave16991.BranchOracle
noncomputable section
open GlobalHard GlobalHardEuclidean
open scoped BigOperators InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048
set_option maxSynthPendingDepth 4
set_option maxHeartbeats 1000000

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def layerCast {a b : ℕ} (h : a = b) : FormalLayer (ι := ι) E a ≃ₗᵢ[ℝ] FormalLayer (ι := ι) E b := by
  cases h
  exact LinearIsometryEquiv.refl ℝ _

def selectAtDepth {I Z : Type*} [Fintype I] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (depth : I → ℕ) (P : ∀ i, Z →L[ℝ] FormalLayer (ι := ι) E (depth i)) (t : ℕ) :
    Z →L[ℝ] FormalLayer (ι := ι) E t :=
  ∑ i, if h : depth i = t then (layerCast E h).toContinuousLinearEquiv.toContinuousLinearMap.comp (P i) else 0

theorem selectAtDepth_at {I Z : Type*} [Fintype I] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (depth : I → ℕ) (hinj : Function.Injective depth) (P : ∀ i, Z →L[ℝ] FormalLayer (ι := ι) E (depth i)) (i : I) :
    selectAtDepth E depth P (depth i) = P i := by
  classical
  unfold selectAtDepth
  rw [Finset.sum_eq_single i]
  · simp [layerCast]
  · intro j _ hji
    have hj : depth j ≠ depth i := fun h ↦ hji (hinj h)
    simp only [dif_neg hj]
  · simp

def macroRoot (m : ℕ) {M : ℕ} (j : Fin M) : ℕ := j.val * (m + 1)

theorem macroRoot_injective (m M : ℕ) : Function.Injective (macroRoot (M := M) m) := by
  intro i j h
  apply Fin.ext
  exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < m + 1) h

def interiorDepth (m : ℕ) {M : ℕ} (p : Fin M × Fin (m + 1)) : ℕ := p.1.val * (m + 1) + p.2.val

theorem interiorDepth_injective (m M : ℕ) : Function.Injective (interiorDepth (M := M) m) := by
  intro p q h
  apply finProdFinEquiv.injective
  apply Fin.ext
  simpa only [finProdFinEquiv_apply_val, interiorDepth, Nat.mul_comm, Nat.add_comm] using h

variable (M m : ℕ)

def stateMarks (t : ℕ) : GlobalHard.Joint (MacroSpaces (ι := ι) E M m) →L[ℝ] FormalLayer (ι := ι) E t :=
  selectAtDepth E (macroSite (M := M) m) (fun j ↦ stateProj (MacroSpaces (ι := ι) E M m) j) t

def entranceMarks (t : ℕ) : GlobalHard.Joint (MacroSpaces (ι := ι) E M m) →L[ℝ] FormalLayer (ι := ι) E t :=
  selectAtDepth E (macroRoot (M := M) m) (fun j ↦ aProj (MacroSpaces (ι := ι) E M m) j) t

def exitMarks (t : ℕ) : GlobalHard.Joint (MacroSpaces (ι := ι) E M m) →L[ℝ] FormalLayer (ι := ι) E t :=
  selectAtDepth E (macroSite (M := M) m) (fun j ↦ bProj (MacroSpaces (ι := ι) E M m) j) t

def interiorDualMarks (t : ℕ) : GlobalHard.Joint (MacroSpaces (ι := ι) E M m) →L[ℝ] FormalLayer (ι := ι) E t :=
  selectAtDepth E (interiorDepth (M := M) m) (fun p ↦
    (PiLp.proj 2 (MacroSpaces (ι := ι) E M m p.1) p.2.castSucc).comp (dualProj (MacroSpaces (ι := ι) E M m) p.1)) t

def terminalDualMarks (t : ℕ) : GlobalHard.Joint (MacroSpaces (ι := ι) E M m) →L[ℝ] FormalLayer (ι := ι) E t :=
  selectAtDepth E (macroSite (M := M) m) (fun j ↦
    (PiLp.proj 2 (MacroSpaces (ι := ι) E M m j) (Fin.last (m + 1))).comp (dualProj (MacroSpaces (ι := ι) E M m) j)) t

def queryMark (t : ℕ) (slot : Fin 5) : GlobalHard.Joint (MacroSpaces (ι := ι) E M m) →L[ℝ] FormalLayer (ι := ι) E t :=
  match slot.val with
  | 0 => stateMarks E M m t
  | 1 => entranceMarks E M m t
  | 2 => exitMarks E M m t
  | 3 => interiorDualMarks E M m t
  | _ => terminalDualMarks E M m t

theorem queryMark_state (j : Fin M) : queryMark E M m (macroSite m j) 0 = stateProj (MacroSpaces (ι := ι) E M m) j :=
  selectAtDepth_at E _ (macroSite_strictMono m M).injective _ j

theorem queryMark_entrance (j : Fin M) : queryMark E M m (macroRoot m j) 1 = aProj (MacroSpaces (ι := ι) E M m) j :=
  selectAtDepth_at E _ (macroRoot_injective m M) _ j

theorem queryMark_exit (j : Fin M) : queryMark E M m (macroSite m j) 2 = bProj (MacroSpaces (ι := ι) E M m) j :=
  selectAtDepth_at E _ (macroSite_strictMono m M).injective _ j

theorem queryMark_interiorDual (j : Fin M) (k : Fin (m + 1)) :
    queryMark E M m (j.val * (m + 1) + k.val) 3 =
      (PiLp.proj 2 (MacroSpaces (ι := ι) E M m j) k.castSucc).comp (dualProj (MacroSpaces (ι := ι) E M m) j) :=
  selectAtDepth_at E _ (interiorDepth_injective m M) _ (j,k)

theorem queryMark_terminalDual (j : Fin M) : queryMark E M m (macroSite m j) 4 =
    (PiLp.proj 2 (MacroSpaces (ι := ι) E M m j) (Fin.last (m + 1))).comp (dualProj (MacroSpaces (ι := ι) E M m) j) :=
  selectAtDepth_at E _ (macroSite_strictMono m M).injective _ j

variable [FiniteDimensional ℝ E]

def outputMark (t : ℕ) (c : PrimalSpace (primalDimension (MacroSpaces (ι := ι) E M m))) : FormalLayer (ι := ι) E t :=
  markedState (queryMark E M m t 0 (atDual (MacroSpaces (ι := ι) E M m)
    ((primalCoordinates (MacroSpaces (ι := ι) E M m)).symm c) 0))

theorem outputMark_norm_le (t : ℕ) (c : PrimalSpace (primalDimension (MacroSpaces (ι := ι) E M m))) :
    ‖outputMark E M m t c‖ ≤ 1 := markedState_norm_le _

theorem outputMark_source (j : Fin M) (c : PrimalSpace (primalDimension (MacroSpaces (ι := ι) E M m))) :
    outputMark E M m (macroSite m j) c = returnedSourceProbe (MacroSpaces (ι := ι) E M m) j c := by
  unfold outputMark
  rw [queryMark_state]
  rfl

end
end NCConcave16991.BranchOracle
