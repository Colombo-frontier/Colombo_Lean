import FullJet.FiniteProbability
import FullJet.TranscriptInformation
import Mathlib.Data.List.OfFn

open scoped BigOperators

namespace FullJet

variable {Ω β : Type*}

/-- A deterministic observation rule may inspect all previous answers. -/
def validHistory (reply : Ω → List β → β) (ω : Ω) (past : List β) : List β → Prop
  | [] => True
  | b :: bs => reply ω past = b ∧ validHistory reply ω (past ++ [b]) bs

theorem validHistory_append (reply : Ω → List β → β) (ω : Ω)
    (past xs ys : List β) :
    validHistory reply ω past (xs ++ ys) ↔
      validHistory reply ω past xs ∧ validHistory reply ω (past ++ xs) ys := by
  induction xs generalizing past with
  | nil => simp [validHistory]
  | cons b bs ih => simp [validHistory, ih, List.append_assoc, and_assoc]

def historyEvent (reply : Ω → List β → β) (base hist : List β) : Set Ω :=
  {ω | validHistory reply ω base hist}

theorem historyEvent_snoc (reply : Ω → List β → β) (base hist : List β) (b : β) :
    historyEvent reply base (hist ++ [b]) =
      historyEvent reply base hist ∩ {ω | reply ω (base ++ hist) = b} := by
  ext ω
  simp [historyEvent, validHistory_append, validHistory]

noncomputable def historyMass (p : PMF Ω) (reply : Ω → List β → β)
    (base hist : List β) : ℝ := (p.toOuterMeasure (historyEvent reply base hist)).toReal

/-- On impossible histories use the same deterministic default answer. -/
noncomputable def historyKernel (p : PMF Ω) (reply : Ω → List β → β)
    (base : List β) (fallback : β) (hist : List β) : PMF β := by
  classical
  exact if h : ∃ ω ∈ historyEvent reply base hist, ω ∈ p.support then
    (p.filter (historyEvent reply base hist) h).map (fun ω => reply ω (base ++ hist))
  else PMF.pure fallback

noncomputable def historyKernelWeight (p : PMF Ω) (reply : Ω → List β → β)
    (base : List β) (fallback : β) (hist : List β) (b : β) : ℝ :=
  (historyKernel p reply base fallback hist b).toReal

theorem historyKernelWeight_nonneg (p : PMF Ω) (reply : Ω → List β → β)
    (base : List β) (fallback : β) (hist : List β) (b : β) :
    0 ≤ historyKernelWeight p reply base fallback hist b := ENNReal.toReal_nonneg

theorem historyKernelWeight_sum [Fintype β] (p : PMF Ω) (reply : Ω → List β → β)
    (base : List β) (fallback : β) (hist : List β) :
    ∑ b, historyKernelWeight p reply base fallback hist b = 1 :=
  pmf_toReal_sum _

theorem historyMass_nil (p : PMF Ω) (reply : Ω → List β → β) (base : List β) :
    historyMass p reply base [] = 1 := by
  simp [historyMass, historyEvent, validHistory, PMF.toOuterMeasure_apply]

theorem historyMass_snoc [Fintype Ω] (p : PMF Ω) (reply : Ω → List β → β)
    (base hist : List β) (fallback b : β) :
    historyMass p reply base (hist ++ [b]) =
      historyMass p reply base hist * historyKernelWeight p reply base fallback hist b := by
  classical
  by_cases h : ∃ ω ∈ historyEvent reply base hist, ω ∈ p.support
  · unfold historyMass historyKernelWeight historyKernel
    rw [dif_pos h, historyEvent_snoc,
      ← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
    exact pmf_event_chain p _ _ h
  · have hchild : ¬ ∃ ω ∈ historyEvent reply base (hist ++ [b]), ω ∈ p.support := by
      rw [historyEvent_snoc]
      rintro ⟨ω, hω, hp⟩
      exact h ⟨ω, hω.1, hp⟩
    have hzero := pmf_event_zero_of_no_support p _ h
    have hchildzero := pmf_event_zero_of_no_support p _ hchild
    unfold historyMass
    rw [hzero, hchildzero, zero_mul]

theorem historyMass_append_ofFn [Fintype Ω] [Fintype β]
    (p : PMF Ω) (reply : Ω → List β → β) (base : List β) (fallback : β)
    (hist : List β) (q : ℕ) (v : Fin q → β) :
    historyMass p reply base (hist ++ List.ofFn v) =
      historyMass p reply base hist *
        transcriptWeight (historyKernelWeight p reply base fallback) hist q v := by
  induction q generalizing hist with
  | zero => simp [transcriptWeight]
  | succ q ih =>
    rw [List.ofFn_succ]
    have hlist : hist ++ v 0 :: List.ofFn (fun i : Fin q => v i.succ) =
        (hist ++ [v 0]) ++ List.ofFn (fun i : Fin q => v i.succ) :=
      by simp [List.append_assoc]
    rw [hlist]
    rw [ih, historyMass_snoc p reply base hist fallback (v 0)]
    simp only [transcriptWeight, mul_assoc, Fin.tail_def]

/-- The finite answer vector produced by the actual deterministic observation rule. -/
def runReplies (reply : Ω → List β → β) (ω : Ω) (past : List β) :
    (q : ℕ) → (Fin q → β)
  | 0 => Fin.elim0
  | q + 1 => Fin.cons (reply ω past) (runReplies reply ω (past ++ [reply ω past]) q)

theorem validHistory_ofFn (reply : Ω → List β → β) (ω : Ω) (past : List β)
    (q : ℕ) (v : Fin q → β) :
    validHistory reply ω past (List.ofFn v) ↔ runReplies reply ω past q = v := by
  induction q generalizing past with
  | zero => simp [validHistory, runReplies, Subsingleton.elim (Fin.elim0 : Fin 0 → β) v]
  | succ q ih =>
    rw [List.ofFn_succ]
    simp only [validHistory, ih, runReplies]
    rw [← Fin.cons_self_tail v, Fin.cons_inj]
    constructor
    · rintro ⟨h, ht⟩
      exact ⟨h, by simpa only [h] using ht⟩
    · rintro ⟨h, ht⟩
      exact ⟨h, by simpa only [h] using ht⟩

/-- Exact mass of the pushforward of a latent sample under an adaptive run.
No assumption that every history has positive probability is needed. -/
theorem runReplies_mass [Fintype Ω] [Fintype β]
    (p : PMF Ω) (reply : Ω → List β → β) (base : List β) (fallback : β)
    (q : ℕ) (v : Fin q → β) :
    ((p.map (fun ω => runReplies reply ω base q)) v).toReal =
      transcriptWeight (historyKernelWeight p reply base fallback) [] q v := by
  rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
  have hevent : (fun ω => runReplies reply ω base q) ⁻¹' ({v} : Set (Fin q → β)) =
      historyEvent reply base (List.ofFn v) := by
    ext ω
    exact (validHistory_ofFn reply ω base q v).symm
  rw [hevent]
  change historyMass p reply base (List.ofFn v) = _
  simpa only [List.nil_append, historyMass_nil, one_mul] using
    historyMass_append_ofFn p reply base fallback [] q v

end FullJet
