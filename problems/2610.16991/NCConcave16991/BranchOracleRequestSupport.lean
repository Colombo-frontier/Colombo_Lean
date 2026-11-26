import NCConcave16991.BranchOracleRequest
import NCConcave16991.BranchOracleCommonEvent

/-! # The actual mixed request vectors preserve chronological word support -/

namespace NCConcave16991.BranchOracle
noncomputable section
open GlobalHard GlobalHardEuclidean

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (M m : ℕ)

def InverseMarksSupported (p : WordProfile ι) (W : Submodule ℝ E) (marks : InverseMarks (ι := ι) E M m) : Prop :=
  ∀ t slot, marks t slot ∈ wordSupport t.val (p.words t.val) W

theorem forwardMatrixRequest_formal_supported (p : WordProfile ι) (W : Submodule ℝ E)
    (marks : InverseMarks (ι := ι) E M m) (hm : InverseMarksSupported E M m p W marks)
    (i : ι) (j : Fin M) (k : Fin (m + 1)) :
    prepend E (j.val * (m + 1) + k.val) i (marks (depthVertex M m j k.castSucc) 3) ∈
      wordSupport (j.val * (m + 1) + k.val + 1)
        ((p.matrixScheduleStep (fun _ ↦ i)).words (j.val * (m + 1) + k.val + 1)) W := by
  have hx : marks (depthVertex M m j k.castSucc) 3 ∈
      wordSupport (j.val * (m + 1) + k.val) (p.words (j.val * (m + 1) + k.val)) W := by
    simpa only [depthVertex, Fin.val_castSucc] using hm (depthVertex M m j k.castSucc) 3
  exact WordProfile.schedule_forward_mem_wordSupport p W _ (fun _ ↦ i) _ hx

theorem transposeMatrixRequest_formal_supported (p : WordProfile ι) (W : Submodule ℝ E)
    (marks : InverseMarks (ι := ι) E M m) (hm : InverseMarksSupported E M m p W marks)
    (i : ι) (j : Fin M) (k : Fin (m + 1)) :
    slice E (j.val * (m + 1) + k.val) i
        (marks (depthVertex M m j k.succ) (if k.succ.val < m + 1 then 3 else 4)) ∈
      wordSupport (j.val * (m + 1) + k.val)
        ((p.matrixScheduleStep (fun _ ↦ i)).words (j.val * (m + 1) + k.val)) W := by
  let slot : Fin 5 := if k.succ.val < m + 1 then 3 else 4
  have hy : marks (depthVertex M m j k.succ) slot ∈
      wordSupport (j.val * (m + 1) + k.val + 1) (p.words (j.val * (m + 1) + k.val + 1)) W := by
    convert hm (depthVertex M m j k.succ) slot using 1 <;> rfl
  have hh := WordProfile.schedule_transpose_mem_wordSupport p W
    (j.val * (m + 1) + k.val) (fun _ ↦ i) _ hy
  rw [formalBranch_adjoint_apply] at hh
  exact hh

theorem inverseMarksSupported_mono {p q : WordProfile ι} (hpq : WordProfile.WordsExtend p q)
    {W U : Submodule ℝ E} (hWU : W ≤ U) (marks : InverseMarks (ι := ι) E M m)
    (hm : InverseMarksSupported E M m p W marks) : InverseMarksSupported E M m q U marks := by
  intro t slot
  exact wordSupport_mono (hpq t.val) hWU (hm t slot)

variable {n : ℕ} [NeZero n] [FiniteDimensional ℝ E]
variable {D : ℝ} (K : KnownDualDomain (dualDimension (MacroSpaces (ι := Fin n) E M m)) D)
  (Q : ∀ t : ℕ, FormalLayer (ι := Fin n) E t ≃ₗᵢ[ℝ] FormalLayer (ι := Fin n) E t)

theorem querySupported_of_inverseMarks
    (s : Reference.State (n := n) (MacroSpaces (ι := Fin n) E M m) K)
    (q : OracleQuery n (primalDimension (MacroSpaces (ι := Fin n) E M m)) K) (W : Submodule ℝ E)
    (hm : InverseMarksSupported E M m s.profile W
      (queryInverseMarks E M m Q (queryGlobal (MacroSpaces (ι := Fin n) E M m) K q))) :
    Reference.QuerySupported E K Q W s q := by
  intro j
  have hh := hm (depthVertex M m j (Fin.last (m + 1))) 0
  change (Q (macroSite m j)).symm (queryMark E M m (macroSite m j) 0
    (queryGlobal (MacroSpaces (ι := Fin n) E M m) K q)) ∈ _ at hh
  rw [queryMark_state] at hh
  exact hh

theorem outputSupported_of_request (p : WordProfile (Fin n)) (W : Submodule ℝ E)
    (c : PrimalSpace (primalDimension (MacroSpaces (ι := Fin n) E M m)))
    (h : ∀ t : Vertex M m, requestAnswer E M m Q (outputRequest E M m c t) ∈ wordSupport t.val (p.words t.val) W)
    (j : Fin M) :
    (Q (macroSite m j)).symm (returnedSourceProbe (MacroSpaces (ι := Fin n) E M m) j c) ∈
      wordSupport (macroSite m j) (p.words (macroSite m j)) W := by
  have hh := h (depthVertex M m j (Fin.last (m + 1)))
  rw [outputRequest_source] at hh
  exact hh

end
end NCConcave16991.BranchOracle
