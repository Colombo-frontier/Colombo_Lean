import NCConcave16991.DenseSmoothCensoredProbability
import NCConcave16991.DenseSmoothRevelationCosts
import NCConcave16991.DenseWeakFreshCompilerTrace

/-! # Fresh-row reads are bounded by the actual assigned-call cost -/

noncomputable section

namespace NCConcave16991.DenseSmooth.Revelation

open DenseWeakHiding

set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (n T : ℕ) (hn : 0 < n) (ρ : ℝ) (hρ : 0 < ρ)
  {Ω : Type*} [MeasurableSpace Ω]
  (P : OraclePolicy.AdaptivePolicy (Domain n T hn ρ hρ) (n := n)
    (dx := primalDimension E T) Ω)

theorem censoredAdvance_cost (seed : Ω) (s : State E n T hn ρ hρ) (a : E)
    (j : Fin (T + 1)) (hj : frontier E n T hn ρ hρ s = j.val) :
    s.assigned j + (censoredRequest E n T hn ρ hρ P seed s).elim 0 (fun _ ↦ 1) ≤
      (censoredAdvance E n T hn ρ hρ P seed s a).assigned j := by
  have hf : frontier E n T hn ρ hρ s < T + 1 := hj ▸ j.isLt
  have hi : stageIndex E n T hn ρ hρ s = j :=
    Fin.ext ((Nat.mod_eq_of_lt hf).trans hj)
  have hbound : (censoredRequest E n T hn ρ hρ P seed s).elim 0 (fun _ ↦ 1) ≤ 1 := by
    cases censoredRequest E n T hn ρ hρ P seed s <;> simp
  unfold censoredAdvance precompletionStep step
  cases ha : action E n T hn ρ hρ P seed s with
  | inl x =>
      have hr : censoredRequest E n T hn ρ hρ P seed s = none := by
        simp [censoredRequest,freshRequest,request,ha]
      simp only [Sum.elim_inl,hr,Option.elim_none,Nat.add_zero,le_refl]
  | inr o =>
      simp only [Sum.elim_inr]
      rw [paidQuery_assigned,if_pos hf,hi,Function.update_self]
      omega

theorem censoredAdvance_frontier (seed : Ω) (s : State E n T hn ρ hρ) (a : E) :
    frontier E n T hn ρ hρ (censoredAdvance E n T hn ρ hρ P seed s a) =
      frontier E n T hn ρ hρ s :=
  precompletionStep_frontier E n T hn ρ hρ P seed s _

section GenericCost

variable {S : Type*} {N D : ℕ}
  (req : S → Option (Fin N)) (adv : S → FreshCompiler.Reply D → S)
  (cost : S → ℕ) (valid : S → Prop)

theorem freshReads_le_cost (table : Fin N → FreshCompiler.Reply D)
    (hstep : ∀ s a, valid s → cost s + (req s).elim 0 (fun _ ↦ 1) ≤ cost (adv s a))
    (hvalid : ∀ s a, valid s → valid (adv s a)) (t : ℕ) (s : S) (hs : valid s) :
    FreshCompiler.readsBefore req adv table t s + cost s ≤
      cost (FreshCompiler.actualRun req adv table t s) := by
  induction t generalizing s with
  | zero => simp [FreshCompiler.readsBefore,FreshCompiler.actualRun]
  | succ t ih =>
      have hv : valid (FreshCompiler.actualStep req adv table s) := hvalid _ _ hs
      have hc : cost s + (req s).elim 0 (fun _ ↦ 1) ≤
          cost (FreshCompiler.actualStep req adv table s) := hstep _ _ hs
      have hh := ih _ hv
      cases hr : req s <;>
        simp only [FreshCompiler.readsBefore,hr,FreshCompiler.actualRun,Option.elim_none,
          Option.elim_some] at hc ⊢ <;> omega

end GenericCost

variable (D : ℕ)
  (Q : OraclePolicy.AdaptivePolicy (Domain n T hn ρ hρ) (n := n)
    (dx := primalDimension (CensoredSpace D) T) Ω)

theorem bits_reads_le_cost (seed : Ω) (table : Fin n → FreshCompiler.Reply D)
    (t : ℕ) (s : State (CensoredSpace D) n T hn ρ hρ) (j : Fin (T + 1))
    (hj : frontier (CensoredSpace D) n T hn ρ hρ s = j.val) :
    FreshCompiler.readsBefore (bitsRequest n T D hn ρ hρ Q seed)
      (bitsAdvance n T D hn ρ hρ Q seed) table t s + s.assigned j ≤
      (FreshCompiler.actualRun (bitsRequest n T D hn ρ hρ Q seed)
        (bitsAdvance n T D hn ρ hρ Q seed) table t s).assigned j := by
  exact freshReads_le_cost _ _ (fun s ↦ s.assigned j)
    (fun s ↦ frontier (CensoredSpace D) n T hn ρ hρ s = j.val) table
    (fun s a hs ↦ censoredAdvance_cost (CensoredSpace D) n T hn ρ hρ Q seed s _ j hs)
    (fun s a hs ↦ (censoredAdvance_frontier (CensoredSpace D) n T hn ρ hρ Q seed s _).trans hs) t s hj

def initializedCost (j : Fin (T + 1)) :
    Unit ⊕ State (CensoredSpace D) n T hn ρ hρ → ℕ
  | .inl _ => 0
  | .inr s => s.assigned j + 1

def initializedValid (j : Fin (T + 1)) :
    Unit ⊕ State (CensoredSpace D) n T hn ρ hρ → Prop
  | .inl _ => True
  | .inr s => frontier (CensoredSpace D) n T hn ρ hρ s = j.val

theorem initialized_reads_le_cost (seed : Ω) (i₀ : Fin n)
    (start : CensoredSpace D → State (CensoredSpace D) n T hn ρ hρ)
    (j : Fin (T + 1))
    (hstart : ∀ a, frontier (CensoredSpace D) n T hn ρ hρ (start a) = j.val)
    (table : Fin n → FreshCompiler.Reply D) (t : ℕ) :
    FreshCompiler.readsBefore (initializedBitsRequest n T D hn ρ hρ Q seed i₀)
      (initializedBitsAdvance n T D hn ρ hρ Q seed start) table t (.inl ()) ≤
      initializedCost n T hn ρ hρ D j
        (FreshCompiler.actualRun (initializedBitsRequest n T D hn ρ hρ Q seed i₀)
          (initializedBitsAdvance n T D hn ρ hρ Q seed start) table t (.inl ())) := by
  apply freshReads_le_cost _ _ (initializedCost n T hn ρ hρ D j)
    (initializedValid n T hn ρ hρ D j) table ?_ ?_ t (.inl ()) trivial
  · intro s a hs
    cases s with
    | inl u =>
        simp only [initializedCost,initializedBitsRequest,initializedBitsAdvance,
          FreshCompiler.initializedRequest,FreshCompiler.initializedAdvance,Option.elim_some]
        omega
    | inr s =>
        have hh := censoredAdvance_cost (CensoredSpace D) n T hn ρ hρ Q seed s (normalizedReply a) j hs
        change s.assigned j + 1 + (bitsRequest n T D hn ρ hρ Q seed s).elim 0 (fun _ ↦ 1) ≤
          (bitsAdvance n T D hn ρ hρ Q seed s a).assigned j + 1
        change s.assigned j + 1 + (censoredRequest (CensoredSpace D) n T hn ρ hρ Q seed s).elim 0 (fun _ ↦ 1) ≤
          (censoredAdvance (CensoredSpace D) n T hn ρ hρ Q seed s (normalizedReply a)).assigned j + 1
        omega
  · intro s a hs
    cases s with
    | inl u => exact hstart _
    | inr s => exact (censoredAdvance_frontier (CensoredSpace D) n T hn ρ hρ Q seed s _).trans hs

end NCConcave16991.DenseSmooth.Revelation
