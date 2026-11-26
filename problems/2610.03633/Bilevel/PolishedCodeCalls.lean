import Bilevel.CachedOracleCodeAlgorithm
import Bilevel.CachedOuterTotalCalls

/-! Pointwise counters for the public oracle language.  The reply function
and its stream are arbitrary; no probability law, moment bound or good event
is assumed.  These certificates concern actual executions, not arbitrary
tuples with a fabricated cost coordinate. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Bilevel.OracleCode
open Stateful

variable {Q O A B C I : Space} {Seed : Type}

def ExactCalls (response : Q → Seed → O) (c : Code Q O A B) (n : ℕ) : Prop :=
  ∀ z : A × IndependentStream.Stream Seed, (eval response c z).1.2.2 = n

theorem exactCalls_pure (response : Q → Seed → O) (f : A → B) (hf : Measurable f) :
    ExactCalls response (.pure f hf) 0 := fun _ => rfl

theorem exactCalls_call (response : Q → Seed → O) :
    ExactCalls response (.call : Code Q O Q O) 1 := fun _ => rfl

theorem ExactCalls.bind {response : Q → Seed → O} {p : Code Q O A B}
    {q : Code Q O (prod A B) C} {m n : ℕ}
    (hp : ExactCalls response p m) (hq : ExactCalls response q n) :
    ExactCalls response (.bind p q) (m+n) := by
  intro z
  change (eval response p z).1.2.2 +
    (eval response q ((z.1,(eval response p z).1.1),(eval response p z).2)).1.2.2 = _
  rw [hp,hq]

theorem ExactCalls.reparam {response : Q → Seed → O} {p : Code Q O A B} {n : ℕ}
    (hp : ExactCalls response p n) (f : I → A) (hf : Measurable f) :
    ExactCalls response (.reparam p f hf) n := fun z => hp (f z.1,z.2)

theorem ExactCalls.map {response : Q → Seed → O} {p : Code Q O A B} {n : ℕ}
    (hp : ExactCalls response p n) (f : prod A B → C) (hf : Measurable f) :
    ExactCalls response (map p f hf) n := by
  simpa only [Nat.add_zero] using hp.bind (exactCalls_pure response f hf)

theorem exactCalls_read (response : Q → Seed → O) (r : O → B) (hr : Measurable r) :
    ExactCalls response (read r hr) 1 :=
  (exactCalls_call response).map _ _

section Batch
variable {E : Space} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [BorelSpace E] [SecondCountableTopology E]

theorem exactCalls_sum (response : Q → Seed → O) (r : O → E) (hr : Measurable r)
    (n : ℕ) : ExactCalls response (sum r hr n) n := by
  induction n with
  | zero => exact exactCalls_pure response _ _
  | succ n ih =>
    exact ih.bind (((exactCalls_read response r hr).reparam _ _).map _ _)

theorem exactCalls_batch (response : Q → Seed → O) (r : O → E) (hr : Measurable r)
    (n : ℕ) : ExactCalls response (batch r hr n) n :=
  (exactCalls_sum response r hr n).map _ _
end Batch

section Confidence
variable {E : Type} [NormedAddCommGroup E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E]

omit [NormedAddCommGroup E] [BorelSpace E] [SecondCountableTopology E] in
theorem exactCalls_collect {response : Q → Seed → O} {c : Code Q O A (of E)}
    {m : ℕ} (hc : ExactCalls response c m) (n : ℕ) :
    ExactCalls response (collect c n) (n*m) := by
  induction n with
  | zero =>
    simpa only [collect,Nat.zero_mul] using
      (exactCalls_pure (A:=A) (B:=of (Fin 0 → E)) response (fun _ => Fin.elim0) (by fun_prop))
  | succ n ih =>
    have hs : ExactCalls response (collectStep c n) m :=
      (hc.reparam (I:=prod A (of (Fin n → E))) Prod.fst measurable_fst).map
        (C:=of (Fin (n+1) → E)) (StatefulConfidence.append n)
        (StatefulConfidence.append_measurable n)
    simpa only [Nat.add_mul,Nat.one_mul] using ih.bind hs

theorem exactCalls_amplify {response : Q → Seed → O} {c : Code Q O A (of E)}
    {m : ℕ} (hc : ExactCalls response c m) (n : ℕ) [NeZero n] :
    ExactCalls response (amplify c n) (n*m) :=
  (exactCalls_collect hc n).map _ _
end Confidence

section Accelerated
open AcceleratedInner
variable {Param : Space} {E : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (response : Q → Seed → O) (r : O → E) (hr : Measurable r)
  (loc : Param × E → Q) (hloc : Measurable loc)
  (shift : Param → E) (hshift : Measurable shift)

theorem exactCalls_acceleratedStep (μ M α : ℝ) (B : ℕ) :
    ExactCalls response (acceleratedStep r hr loc hloc shift hshift μ M α B) B := by
  unfold acceleratedStep
  exact ((exactCalls_batch (E:=of E) response r hr B).reparam _ _).map _ _

theorem exactCalls_acceleratedRun (μ M α : ℝ) (B n : ℕ) :
    ExactCalls response (acceleratedRun r hr loc hloc shift hshift μ M α B n) (n*B) := by
  induction n with
  | zero =>
    simpa only [acceleratedRun,Nat.zero_mul] using
      (exactCalls_pure (A:=of (Param × (E × E))) (B:=of (E × E)) response Prod.snd measurable_snd)
  | succ n ih =>
    simpa only [Nat.add_mul,Nat.one_mul] using
      ih.bind ((exactCalls_acceleratedStep response r hr loc hloc shift hshift μ M α B).reparam _ _)

theorem exactCalls_acceleratedStages (μ M α σ U : ℝ) (n : ℕ) :
    ExactCalls response (acceleratedStages r hr loc hloc shift hshift μ M α σ U n)
      (stageLength α * ∑ s ∈ Finset.range n,stageBatch M α σ (stageBudget U (s+1))) := by
  induction n with
  | zero =>
    simpa only [acceleratedStages,Finset.sum_range_zero,Nat.mul_zero] using
      (exactCalls_pure (A:=of (Param × (E × E))) (B:=of (E × E)) response Prod.snd measurable_snd)
  | succ n ih =>
    simpa only [Finset.sum_range_succ,Nat.mul_add] using ih.bind
      ((exactCalls_acceleratedRun response r hr loc hloc shift hshift μ M α
        (stageBatch M α σ (stageBudget U (n+1))) (stageLength α)).reparam _ _)

theorem exactCalls_acceleratedSolve (μ M α σ R radius : ℝ) :
    ExactCalls response (acceleratedSolve r hr loc hloc shift hshift μ M α σ R radius)
      (StatefulAccelerated.solveCalls μ M α σ R radius) := by
  unfold acceleratedSolve StatefulAccelerated.solveCalls
  split_ifs
  · exact exactCalls_pure response _ _
  · exact ((exactCalls_acceleratedStages response r hr loc hloc shift hshift μ M α σ
      (M*R^2) _).reparam _ _).map _ _
end Accelerated
end Bilevel.OracleCode
