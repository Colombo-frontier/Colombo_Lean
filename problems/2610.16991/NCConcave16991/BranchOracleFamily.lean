import NCConcave16991.BranchOracleFormalLayer
import NCConcave16991.BranchConstructionRotations

/-! # The literal shared-depth macro family and propagated physical sources -/

namespace NCConcave16991.BranchOracle
noncomputable section
open scoped InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

abbrev MacroSpaces (M m : ℕ) (j : Fin M) (k : Fin ((m + 1) + 1)) :=
  FormalLayer (ι := ι) E (j.val * (m + 1) + k.val)

def macroFormalBranches {M m : ℕ} (j : Fin M) (t : Fin (m + 1)) :
    BranchGeometry.BranchFamily (ι := ι) (MacroSpaces (ι := ι) E M m j t.castSucc)
      (MacroSpaces (ι := ι) E M m j t.succ) :=
  formalBranchFamily E (j.val * (m + 1) + t.val)

def macroRotations {M m : ℕ}
    (Q : ∀ d : ℕ, FormalLayer (ι := ι) E d ≃ₗᵢ[ℝ] FormalLayer (ι := ι) E d)
    (j : Fin M) (k : Fin ((m + 1) + 1)) :
    MacroSpaces (ι := ι) E M m j k ≃ₗᵢ[ℝ] MacroSpaces (ι := ι) E M m j k :=
  Q (j.val * (m + 1) + k.val)

def macroBranches {M m : ℕ}
    (Q : ∀ d : ℕ, FormalLayer (ι := ι) E d ≃ₗᵢ[ℝ] FormalLayer (ι := ι) E d)
    (j : Fin M) : ∀ t : Fin (m + 1),
    BranchGeometry.BranchFamily (ι := ι) (MacroSpaces (ι := ι) E M m j t.castSucc)
      (MacroSpaces (ι := ι) E M m j t.succ) :=
  BranchConstruction.rotatedBranches (MacroSpaces (ι := ι) E M m j) (macroFormalBranches E j) (macroRotations E Q j)

def incomingSources {M m : ℕ}
    (Q : ∀ d : ℕ, FormalLayer (ι := ι) E d ≃ₗᵢ[ℝ] FormalLayer (ι := ι) E d) (e : E)
    (j : Fin M) : MacroSpaces (ι := ι) E M m j 0 :=
  Q (j.val * (m + 1)) (formalTarget E (j.val * (m + 1)) e)

def terminalSources {M m : ℕ}
    (Q : ∀ d : ℕ, FormalLayer (ι := ι) E d ≃ₗᵢ[ℝ] FormalLayer (ι := ι) E d) (e : E)
    (j : Fin M) : MacroSpaces (ι := ι) E M m j (Fin.last (m + 1)) :=
  Q (j.val * (m + 1) + (m + 1)) (formalTarget E (j.val * (m + 1) + (m + 1)) e)

theorem macroFormal_propagation {M m : ℕ} (j : Fin M) (k : Fin ((m + 1) + 1)) (e : E) :
    BranchConstruction.propagation (MacroSpaces (ι := ι) E M m j) (macroFormalBranches E j) k
      (formalTarget E (j.val * (m + 1)) e) =
      formalTarget E (j.val * (m + 1) + k.val) e := by
  induction k using Fin.induction with
  | zero => simp [BranchConstruction.propagation_zero]
  | succ t ih =>
    rw [BranchConstruction.propagation_succ]
    change (macroFormalBranches E j t).normalizedIsometry
      (BranchConstruction.propagation (MacroSpaces (ι := ι) E M m j) (macroFormalBranches E j) t.castSucc
        (formalTarget E (j.val * (m + 1)) e)) = _
    rw [ih]
    exact formalTarget_forward E (j.val * (m + 1) + t.val) e

theorem incomingSources_unit {M m : ℕ}
    (Q : ∀ d : ℕ, FormalLayer (ι := ι) E d ≃ₗᵢ[ℝ] FormalLayer (ι := ι) E d) (e : E) (he : ‖e‖ = 1)
    (j : Fin M) : ‖incomingSources (m := m) E Q e j‖ = 1 := by
  exact ((Q (j.val * (m + 1))).norm_map _).trans ((formalTarget_norm E _ e).trans he)

theorem terminalSources_unit {M m : ℕ}
    (Q : ∀ d : ℕ, FormalLayer (ι := ι) E d ≃ₗᵢ[ℝ] FormalLayer (ι := ι) E d) (e : E) (he : ‖e‖ = 1)
    (j : Fin M) : ‖terminalSources (m := m) E Q e j‖ = 1 := by
  exact ((Q (j.val * (m + 1) + (m + 1))).norm_map _).trans ((formalTarget_norm E _ e).trans he)

/-- The actual source vectors satisfy the terminal propagation condition. -/
theorem terminalSources_propagated {M m : ℕ}
    (Q : ∀ d : ℕ, FormalLayer (ι := ι) E d ≃ₗᵢ[ℝ] FormalLayer (ι := ι) E d) (e : E)
    (j : Fin M) :
    terminalSources E Q e j = BranchConstruction.terminalTransport (MacroSpaces (ι := ι) E M m j)
      (macroBranches E Q j) (incomingSources E Q e j) := by
  have hh := BranchConstruction.propagation_rotated (MacroSpaces (ι := ι) E M m j)
    (macroFormalBranches E j) (macroRotations E Q j) (Fin.last (m + 1))
    (formalTarget E (j.val * (m + 1)) e)
  rw [macroFormal_propagation] at hh
  exact hh.symm

end
end NCConcave16991.BranchOracle
