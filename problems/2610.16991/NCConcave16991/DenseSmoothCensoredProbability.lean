import NCConcave16991.DenseWeakFreshCompilerLearned
import NCConcave16991.DenseWeakFreshCompilerProbability
import NCConcave16991.DenseSmoothRevelationFresh
import NCConcave16991.DenseSmoothSigns

/-! # Actual static-bank probability for the concrete censored smooth reference -/

noncomputable section

open scoped BigOperators

namespace NCConcave16991.DenseSmooth.Revelation

open DenseWeakHiding

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

abbrev CensoredSpace (D : ℕ) := EuclideanSpace ℝ (Fin D)

def normalizedReply {D : ℕ} (a : FreshCompiler.Reply D) : CensoredSpace D :=
  normalizedSignVector (fun d ↦ hiddenSign (a d))

theorem normalizedReply_row {n m D : ℕ} (bank : ColumnBank n m D) (i : Fin n) :
    normalizedReply (fun d ↦ columnBit (bank d) i) =
      normalizedSignVector (fun d ↦ columnSign (bank d).2.val i) := by
  unfold normalizedReply
  congr 1
  funext d
  exact columnBit_sign (bank d) i

variable (n T D : ℕ) (hn : 0 < n) (ρ : ℝ) (hρ : 0 < ρ)
  {Ω : Type*} [MeasurableSpace Ω]
  (P : OraclePolicy.AdaptivePolicy (Domain n T hn ρ hρ) (n := n)
    (dx := primalDimension (CensoredSpace D) T) Ω)

def bitsRequest (seed : Ω) : State (CensoredSpace D) n T hn ρ hρ → Option (Fin n) :=
  censoredRequest (CensoredSpace D) n T hn ρ hρ P seed

def bitsAdvance (seed : Ω) (s : State (CensoredSpace D) n T hn ρ hρ)
    (a : FreshCompiler.Reply D) : State (CensoredSpace D) n T hn ρ hρ :=
  censoredAdvance (CensoredSpace D) n T hn ρ hρ P seed s (normalizedReply a)

theorem censoredAdvance_none_eq (seed : Ω) (s : State (CensoredSpace D) n T hn ρ hρ)
    (hs : bitsRequest n T D hn ρ hρ P seed s = none) (a b : CensoredSpace D) :
    censoredAdvance (CensoredSpace D) n T hn ρ hρ P seed s a =
      censoredAdvance (CensoredSpace D) n T hn ρ hρ P seed s b := by
  unfold censoredAdvance
  congr 1
  unfold effectiveAnswer Machine.effectiveAnswer
  simp only [← request_eq_machine]
  cases hr : request (CensoredSpace D) n T hn ρ hρ P seed s with
  | none => simp [hr]
  | some ji =>
      by_cases hi : ji.2 ∈ s.base.progress.2
      · simp [hr,hi]
      · have hc : bitsRequest n T D hn ρ hρ P seed s = some ji.2 := by
          simp [bitsRequest,censoredRequest,freshRequest,hr,hi,Option.filter]
        rw [hs] at hc
        contradiction

def initializedLearned : Unit ⊕ State (CensoredSpace D) n T hn ρ hρ → Finset (Fin n)
  | .inl _ => ∅
  | .inr s => s.base.progress.2

def initializedBitsRequest (seed : Ω) (i₀ : Fin n) :=
  FreshCompiler.initializedRequest (bitsRequest n T D hn ρ hρ P seed) i₀

def initializedBitsAdvance (seed : Ω)
    (start : CensoredSpace D → State (CensoredSpace D) n T hn ρ hρ) :=
  FreshCompiler.initializedAdvance (bitsAdvance n T D hn ρ hρ P seed)
    (fun a ↦ start (normalizedReply a))

theorem initializedBits_learned_update (seed : Ω) (i₀ : Fin n)
    (start : CensoredSpace D → State (CensoredSpace D) n T hn ρ hρ)
    (hstart : ∀ a, (start a).base.progress.2 = {i₀})
    (s : Unit ⊕ State (CensoredSpace D) n T hn ρ hρ) (a : FreshCompiler.Reply D) :
    initializedLearned n T D hn ρ hρ (initializedBitsAdvance n T D hn ρ hρ P seed start s a) =
      (initializedBitsRequest n T D hn ρ hρ P seed i₀ s).elim
        (initializedLearned n T D hn ρ hρ s) (fun i ↦ insert i (initializedLearned n T D hn ρ hρ s)) := by
  cases s with
  | inl u => simp [initializedLearned,initializedBitsAdvance,initializedBitsRequest,
      FreshCompiler.initializedAdvance,FreshCompiler.initializedRequest,hstart]
  | inr s =>
      exact censoredAdvance_seen (CensoredSpace D) n T hn ρ hρ P seed s (normalizedReply a)

theorem initializedBits_request_fresh (seed : Ω) (i₀ : Fin n)
    (s : Unit ⊕ State (CensoredSpace D) n T hn ρ hρ) (i : Fin n)
    (hi : initializedBitsRequest n T D hn ρ hρ P seed i₀ s = some i) :
    i ∉ initializedLearned n T D hn ρ hρ s := by
  cases s with
  | inl u => simp [initializedLearned]
  | inr s => exact censoredRequest_fresh (CensoredSpace D) n T hn ρ hρ P seed s i hi

/-- The cache invariant discharges compiler freshness for every actual bank,
including the predetermined initialization row. -/
theorem initializedBits_freshAlong (seed : Ω) (i₀ : Fin n)
    (start : CensoredSpace D → State (CensoredSpace D) n T hn ρ hρ)
    (hstart : ∀ a, (start a).base.progress.2 = {i₀})
    (table : Fin n → FreshCompiler.Reply D) (fuel r : ℕ) :
    FreshCompiler.FreshAlong (initializedBitsRequest n T D hn ρ hρ P seed i₀)
      (initializedBitsAdvance n T D hn ρ hρ P seed start) hn table
      (FreshCompiler.initial fuel (.inl () : Unit ⊕ State (CensoredSpace D) n T hn ρ hρ)) r := by
  exact FreshCompiler.freshAlong_of_learned _ _ (initializedLearned n T D hn ρ hρ)
    (initializedBits_learned_update n T D hn ρ hρ P seed i₀ start hstart) hn table fuel (.inl ()) rfl
    (initializedBits_request_fresh n T D hn ρ hρ P seed i₀) r

def initializedProbe (v : State (CensoredSpace D) n T hn ρ hρ → Fin D → ℝ) :
    Unit ⊕ State (CensoredSpace D) n T hn ρ hρ → Fin D → ℝ
  | .inl _ => fun _ ↦ 0
  | .inr s => v s

/-- A concrete censored reference, including its selected initialization row,
has alignment probability at most 1/8 under the original static bank. -/
theorem censored_alignment_probability_le {m : ℕ} (hm : m ≤ n)
    (hparity : m % 2 = n % 2) (seed : Ω) (i₀ : Fin n)
    (start : CensoredSpace D → State (CensoredSpace D) n T hn ρ hρ)
    (hstart : ∀ a, (start a).base.progress.2 = {i₀}) (fuel r : ℕ)
    (hrn : r < n) (hbudget : 8 * m + 9 * r ≤ n)
    (hcoef : (32 / 63 : ℝ) * r * ((m : ℝ) / ((n : ℝ) - r)) ^ 2 ≤ 1 / 8000)
    (v : State (CensoredSpace D) n T hn ρ hρ → Fin D → ℝ)
    (hv : ∀ s, (∑ j, (v s j) ^ 2) ≤ 1)
    (hD : 512 * Real.log (((fuel + 1 : ℕ) : ℝ) + 2) + 2048 ≤ (D : ℝ)) :
    (columnBankLaw n m D hm).eventMass {bank |
      ∃ s ∈ FreshCompiler.cutTrace (initializedBitsRequest n T D hn ρ hρ P seed i₀)
        (initializedBitsAdvance n T D hn ρ hρ P seed start)
        (fun i d ↦ columnBit (bank d) i) r fuel (.inl ()),
      (5 / 32 : ℝ) * Real.sqrt (D : ℝ) ≤ signedSum
        (initializedProbe n T D hn ρ hρ v s) (bankLabels bank)} ≤ 1 / 8 := by
  let req := initializedBitsRequest n T D hn ρ hρ P seed i₀
  let adv := initializedBitsAdvance n T D hn ρ hρ P seed start
  let probe := initializedProbe n T D hn ρ hρ v
  have hp := FreshCompiler.cutTrace_alignment_probability_le req adv hn hm hparity fuel (.inl ()) r
    hrn hbudget hcoef probe (by
      intro s
      cases s with
      | inl u => simp [probe,initializedProbe]
      | inr s => exact hv s) hD
  apply (FiniteLaw.eventMass_mono (columnBankLaw n m D hm) ?_).trans hp
  intro bank hb
  exact ⟨initializedBits_freshAlong n T D hn ρ hρ P seed i₀ start hstart _ fuel r,hb⟩

theorem bits_freshAlong (seed : Ω) (s : State (CensoredSpace D) n T hn ρ hρ)
    (hs : s.base.progress.2 = ∅) (table : Fin n → FreshCompiler.Reply D) (fuel r : ℕ) :
    FreshCompiler.FreshAlong (bitsRequest n T D hn ρ hρ P seed)
      (bitsAdvance n T D hn ρ hρ P seed) hn table (FreshCompiler.initial fuel s) r := by
  exact FreshCompiler.freshAlong_of_learned _ _ (fun s ↦ s.base.progress.2)
    (fun s a ↦ censoredAdvance_seen (CensoredSpace D) n T hn ρ hρ P seed s (normalizedReply a))
    hn table fuel s hs (fun s i hi ↦ censoredRequest_fresh (CensoredSpace D) n T hn ρ hρ P seed s i hi) r

/-- Stage zero has no initialization read and starts with an empty cache. -/
theorem censored_empty_alignment_probability_le {m : ℕ} (hm : m ≤ n)
    (hparity : m % 2 = n % 2) (seed : Ω) (s : State (CensoredSpace D) n T hn ρ hρ)
    (hs : s.base.progress.2 = ∅) (fuel r : ℕ) (hrn : r < n) (hbudget : 8 * m + 9 * r ≤ n)
    (hcoef : (32 / 63 : ℝ) * r * ((m : ℝ) / ((n : ℝ) - r)) ^ 2 ≤ 1 / 8000)
    (v : State (CensoredSpace D) n T hn ρ hρ → Fin D → ℝ)
    (hv : ∀ s, (∑ j, (v s j) ^ 2) ≤ 1)
    (hD : 512 * Real.log (((fuel + 1 : ℕ) : ℝ) + 2) + 2048 ≤ (D : ℝ)) :
    (columnBankLaw n m D hm).eventMass {bank |
      ∃ x ∈ FreshCompiler.cutTrace (bitsRequest n T D hn ρ hρ P seed)
        (bitsAdvance n T D hn ρ hρ P seed) (fun i d ↦ columnBit (bank d) i) r fuel s,
        (5 / 32 : ℝ) * Real.sqrt (D : ℝ) ≤ signedSum (v x) (bankLabels bank)} ≤ 1 / 8 := by
  have hp := FreshCompiler.cutTrace_alignment_probability_le
    (bitsRequest n T D hn ρ hρ P seed) (bitsAdvance n T D hn ρ hρ P seed) hn hm hparity fuel s r
    hrn hbudget hcoef v hv hD
  apply (FiniteLaw.eventMass_mono (columnBankLaw n m D hm) ?_).trans hp
  intro bank hb
  exact ⟨bits_freshAlong n T D hn ρ hρ P seed s hs _ fuel r,hb⟩

end NCConcave16991.DenseSmooth.Revelation
