import GradientHessian.MachineUnboundedPosterior
import LowRank.ProjectorRank

/-! Measurable output normalization removes any validity restriction on
unreachable machine states. Valid actual output projectors are unchanged. -/

namespace GradientHessian.MachinePosterior

open MeasureTheory Matrix LowRank MachineCompiler
noncomputable section

def ValidOutput {d : ℕ} (rank : ℝ) (Q : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  IsOrthogonalProjector Q ∧ Q.trace ≤ rank

theorem validOutput_measurableSet (d : ℕ) (rank : ℝ) :
    MeasurableSet {Q : Matrix (Fin d) (Fin d) ℝ | ValidOutput rank Q} := by
  have hT : MeasurableSet {Q : Matrix (Fin d) (Fin d) ℝ | Qᵀ = Q} := by
    have h : MeasurableSet (⋂ i : Fin d, ⋂ j : Fin d,
        {Q : Matrix (Fin d) (Fin d) ℝ | Q j i = Q i j}) := by
      apply MeasurableSet.iInter
      intro i
      apply MeasurableSet.iInter
      intro j
      exact measurableSet_eq_fun (by fun_prop) (by fun_prop)
    convert h using 1
    ext Q
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro he i j
      exact congrFun (congrFun he i) j
    · intro he
      exact funext fun i => funext fun j => he i j
  have hM : MeasurableSet {Q : Matrix (Fin d) (Fin d) ℝ | Q * Q = Q} := by
    have h : MeasurableSet (⋂ i : Fin d, ⋂ j : Fin d,
        {Q : Matrix (Fin d) (Fin d) ℝ | ∑ k, Q i k * Q k j = Q i j}) := by
      apply MeasurableSet.iInter
      intro i
      apply MeasurableSet.iInter
      intro j
      exact measurableSet_eq_fun (by fun_prop) (by fun_prop)
    convert h using 1
    ext Q
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro he i j
      exact congrFun (congrFun he i) j
    · intro he
      exact funext fun i => funext fun j => he i j
  have ht : Measurable (fun Q : Matrix (Fin d) (Fin d) ℝ => Q.trace) := by
    simp only [Matrix.trace, Matrix.diag]
    fun_prop
  have he : {Q : Matrix (Fin d) (Fin d) ℝ | ValidOutput rank Q} =
      {Q | Qᵀ = Q} ∩ {Q | Q * Q = Q} ∩ {Q | Q.trace ≤ rank} := by
    ext Q
    simp only [ValidOutput, Set.mem_setOf_eq, Set.mem_inter_iff]
    exact ⟨fun h => ⟨⟨h.1.symmetric, h.1.idempotent⟩, h.2⟩,
      fun h => ⟨⟨h.1.1, h.1.2⟩, h.2⟩⟩
  rw [he]
  exact (hT.inter hM).inter (measurableSet_le ht measurable_const)

def sanitize {d : ℕ} (rank : ℝ) (Q : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℝ := by
  classical
  exact if ValidOutput rank Q then Q else 0

theorem sanitize_measurable (d : ℕ) (rank : ℝ) : Measurable (@sanitize d rank) :=
  Measurable.ite (validOutput_measurableSet d rank) measurable_id measurable_const

theorem sanitize_eq {d : ℕ} {rank : ℝ} {Q : Matrix (Fin d) (Fin d) ℝ}
    (h : ValidOutput rank Q) : sanitize rank Q = Q := by
  simp only [sanitize, if_pos h]

theorem sanitize_valid {d : ℕ} {rank : ℝ} (hr : 0 ≤ rank)
    (Q : Matrix (Fin d) (Fin d) ℝ) : ValidOutput rank (sanitize rank Q) := by
  classical
  unfold sanitize
  split_ifs with h
  · exact h
  · exact ⟨⟨by simp, by simp⟩, by simpa using hr⟩

theorem sanitize_zero {d : ℕ} {rank : ℝ} (hr : 0 ≤ rank) :
    sanitize rank (0 : Matrix (Fin d) (Fin d) ℝ) = 0 :=
  sanitize_eq ⟨⟨by simp, by simp⟩, by simpa using hr⟩

def normalizeOutput {d : ℕ} {State : Type*} [MeasurableSpace State]
    (P : Program d State (Matrix (Fin d) (Fin d) ℝ)) (rank : ℝ) :
    Program d State (Matrix (Fin d) (Fin d) ℝ) :=
  { P with
    output := fun s => sanitize rank (P.output s)
    fallback := 0
    output_measurable := (sanitize_measurable d rank).comp P.output_measurable }

theorem normalizeOutput_calls {d : ℕ} {State : Type*} [MeasurableSpace State]
    (P : Program d State (Matrix (Fin d) (Fin d) ℝ)) (rank : ℝ)
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (n : ℕ) (s : State) :
    (normalizeOutput P rank).calls oracle n s = P.calls oracle n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    have hm : (normalizeOutput P rank).mode = P.mode := rfl
    have ht : (normalizeOutput P rank).think = P.think := rfl
    have hn : (normalizeOutput P rank).next = P.next := rfl
    have hq : (normalizeOutput P rank).query = P.query := rfl
    simp only [Program.calls, hm, ht, hn, hq, ih]

theorem normalizeOutput_stopped {d : ℕ} {State : Type*} [MeasurableSpace State]
    (P : Program d State (Matrix (Fin d) (Fin d) ℝ)) {rank : ℝ} (hr : 0 ≤ rank)
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (s : State) :
    readOrZero ((normalizeOutput P rank).stoppedResult oracle s) =
      sanitize rank (readOrZero (P.stoppedResult oracle s)) := by
  classical
  have hstep : (normalizeOutput P rank).step oracle = P.step oracle := rfl
  by_cases h : ∃ n, P.mode ((P.step oracle)^[n] s) = 0
  · have hh : (normalizeOutput P rank).mode
        (((normalizeOutput P rank).step oracle)^[Nat.find h] s) = 0 := by
      rw [hstep]
      exact Nat.find_spec h
    rw [Program.stoppedResult_at_halt _ _ _ _ hh,
      Program.stoppedResult_at_halt P oracle (Nat.find h) s (Nat.find_spec h), hstep]
    rfl
  · have hh : ¬∃ n, (normalizeOutput P rank).mode
        (((normalizeOutput P rank).step oracle)^[n] s) = 0 := by
      rw [hstep]
      exact h
    rw [Program.stoppedResult, dif_neg hh, Program.stoppedResult, dif_neg h]
    simp only [readOrZero, Bool.false_eq_true, if_false, sanitize_zero hr]

/-- The most permissive output formulation: the decoder is unrestricted away
from the actual output transcripts. Projector/rank validity is required only
almost surely for its actual stopped output, and invalid unused values are
measurably replaced by zero inside the proof. -/
theorem actual_output_posterior_overlap (r s q : ℕ) {State Seed : Type*}
    [MeasurableSpace State] [MeasurableSpace Seed]
    (seedLaw : Measure Seed) [IsProbabilityMeasure seedLaw]
    (P : Program (r + q) State (Matrix (Fin (r + q)) (Fin (r + q)) ℝ))
    (initial : MeasurableStateMap Seed State)
    (hs : s ≤ r) (hr : 0 < r) {v : NNReal} (hv : v ≠ 0)
    {rank : ℝ} (hrank : 0 ≤ rank)
    (hout : ∀ᵐ p : Seed × Matrix (Fin (r + q)) (Fin (s + q)) ℝ
        ∂seedLaw.prod (iidMatrixLaw (r + q) (s + q) v),
      ValidOutput rank (readOrZero
        (P.stoppedResult (fun u => (p.2 * p.2ᵀ) *ᵥ u) (initial.1 p.1))))
    (hcap : ∀ seed (X : Matrix (Fin (r + q)) (Fin (s + q)) ℝ) n,
      P.calls (fun u => (X * Xᵀ) *ᵥ u) n (initial.1 seed) ≤ q) :
    (∫ p : Seed × Matrix (Fin (r + q)) (Fin (s + q)) ℝ,
      (readOrZero (P.stoppedResult (fun u => (p.2 * p.2ᵀ) *ᵥ u) (initial.1 p.1)) *
        leftKernelProjector p.2).trace
      ∂seedLaw.prod (iidMatrixLaw (r + q) (s + q) v)) ≤
        2 * ((r : ℝ) - s) * ((q : ℝ) + rank) / r := by
  have h := unbounded_stopped_overlap r s q seedLaw (normalizeOutput P rank) initial
    hs hr hv hrank (fun state => sanitize_valid hrank (P.output state))
    (by intro seed X n; rw [normalizeOutput_calls]; exact hcap seed X n)
  have he : (∫ p : Seed × Matrix (Fin (r + q)) (Fin (s + q)) ℝ,
      (readOrZero ((normalizeOutput P rank).stoppedResult
        (fun u => (p.2 * p.2ᵀ) *ᵥ u) (initial.1 p.1)) * leftKernelProjector p.2).trace
        ∂seedLaw.prod (iidMatrixLaw (r + q) (s + q) v)) =
      (∫ p : Seed × Matrix (Fin (r + q)) (Fin (s + q)) ℝ,
        (readOrZero (P.stoppedResult (fun u => (p.2 * p.2ᵀ) *ᵥ u) (initial.1 p.1)) *
          leftKernelProjector p.2).trace
        ∂seedLaw.prod (iidMatrixLaw (r + q) (s + q) v)) := by
    apply integral_congr_ae
    filter_upwards [hout] with p hp
    rw [normalizeOutput_stopped P hrank, sanitize_eq hp]
  rwa [he] at h

/-- The source's boxed formula, using the actual matrix rank rather than a
trace-cap convention and its dimension/kernel-nullity parameter names. -/
theorem manuscript_machine_overlap (r s q D k outputRank : ℕ) {State Seed : Type*}
    [MeasurableSpace State] [MeasurableSpace Seed]
    (seedLaw : Measure Seed) [IsProbabilityMeasure seedLaw]
    (P : Program (r + q) State (Matrix (Fin (r + q)) (Fin (r + q)) ℝ))
    (initial : MeasurableStateMap Seed State)
    (hs : s ≤ r) (hr : 0 < r) (hD : D = r + q) (hk : k + s = r)
    {v : NNReal} (hv : v ≠ 0)
    (hout : ∀ᵐ p : Seed × Matrix (Fin (r + q)) (Fin (s + q)) ℝ
        ∂seedLaw.prod (iidMatrixLaw (r + q) (s + q) v),
      let R := readOrZero (P.stoppedResult (fun u => (p.2 * p.2ᵀ) *ᵥ u) (initial.1 p.1))
      IsOrthogonalProjector R ∧ R.rank ≤ outputRank)
    (hcap : ∀ seed (X : Matrix (Fin (r + q)) (Fin (s + q)) ℝ) n,
      P.calls (fun u => (X * Xᵀ) *ᵥ u) n (initial.1 seed) ≤ q) :
    (∫ p : Seed × Matrix (Fin (r + q)) (Fin (s + q)) ℝ,
      (readOrZero (P.stoppedResult (fun u => (p.2 * p.2ᵀ) *ᵥ u) (initial.1 p.1)) *
        leftKernelProjector p.2).trace
      ∂seedLaw.prod (iidMatrixLaw (r + q) (s + q) v)) ≤
        2 * (k : ℝ) * ((q : ℝ) + outputRank) / ((D : ℝ) - q) := by
  have h := actual_output_posterior_overlap r s q seedLaw P initial hs hr hv
    (Nat.cast_nonneg outputRank)
    (by
      filter_upwards [hout] with p hp
      exact ⟨hp.1, hp.1.trace_le_of_rank_le hp.2⟩) hcap
  have hkr : (k : ℝ) + s = r := by exact_mod_cast hk
  have hDr : (D : ℝ) = r + q := by exact_mod_cast hD
  have hk' : (r : ℝ) - s = k := by linarith
  have hD' : (D : ℝ) - q = r := by linarith
  simpa only [hD', hk'] using h

end
end GradientHessian.MachinePosterior
