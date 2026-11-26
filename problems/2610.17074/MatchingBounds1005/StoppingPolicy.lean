import MatchingBounds1005.MinimaxConversion
import MatchingBounds1005.CUPGMeasurableChoice

/-! Measurable early stopping compiled into the fixed-cap oracle model.
Queries continue according to the original policy, while the terminal output
uses only the first stopped prefix. No later response can change that output. -/
noncomputable section
open MeasureTheory

namespace MatchingBounds1005.Model.StoppingPolicy
open CUPG
attribute [local instance] Classical.propDecidable
variable {d : ℕ} {Seed : Type} [MeasurableSpace Seed]

structure Rule (d : ℕ) (Seed : Type) [MeasurableSpace Seed] where
  stop : (n : ℕ) → Seed → (Fin n → Response d) → Prop
  measurable_stop : ∀ n, MeasurableSet {z : Seed × (Fin n → Response d) | stop n z.1 z.2}

/-- Total prefix extraction; the zero extension is never used before the cap. -/
def historyPrefix {m : ℕ} (n : ℕ) (h : Fin m → Response d) : Fin n → Response d :=
  fun i => if hi : i.val < m then h ⟨i.val, hi⟩ else 0

theorem prefix_measurable (m n : ℕ) :
    Measurable (historyPrefix (d := d) (m := m) n) := by
  apply measurable_pi_lambda
  intro i
  by_cases hi : i.val < m
  · simpa only [historyPrefix, hi, dite_true] using measurable_pi_apply (⟨i.val, hi⟩ : Fin m)
  · simp only [historyPrefix, hi, dite_false]
    exact measurable_const

theorem prefix_transcript (A : Algorithm d Seed) (f : Space d → ℝ) (seed : Seed)
    {n m : ℕ} (hnm : n ≤ m) : historyPrefix n (transcript A f seed m) = transcript A f seed n := by
  funext i
  have hi : i.val < m := i.isLt.trans_le hnm
  simp only [historyPrefix, hi, dite_true]
  exact transcript_prefix A f seed hnm i

def predicate (S : Rule d Seed) {m : ℕ} (z : Seed × (Fin m → Response d)) (n : ℕ) : Prop :=
  S.stop n z.1 (historyPrefix n z.2)

theorem predicate_measurable (S : Rule d Seed) (m n : ℕ) :
    MeasurableSet {z : Seed × (Fin m → Response d) | predicate S z n} :=
  (S.measurable_stop n).preimage
    (measurable_fst.prodMk ((prefix_measurable m n).comp measurable_snd))

def index (S : Rule d Seed) {m : ℕ} (z : Seed × (Fin m → Response d)) (T : ℕ) : ℕ :=
  @firstIndex (predicate S z) (Classical.decPred _) T

theorem index_measurable (S : Rule d Seed) (m T : ℕ) :
    Measurable (fun z : Seed × (Fin m → Response d) => index S z T) :=
  measurable_firstIndex (predicate S) (predicate_measurable S m) T

theorem index_le (S : Rule d Seed) {m : ℕ} (z : Seed × (Fin m → Response d)) (T : ℕ) :
    index S z T ≤ T := firstIndex_le _ _

def scan (A : Algorithm d Seed) (S : Rule d Seed) {m : ℕ}
    (z : Seed × (Fin m → Response d)) : ℕ → Space d
  | 0 => A.output 0 z.1 (historyPrefix 0 z.2)
  | n + 1 => if predicate S z (index S z n) then scan A S z n
      else A.output (n + 1) z.1 (historyPrefix (n + 1) z.2)

theorem scan_measurable (A : Algorithm d Seed) (S : Rule d Seed) (m T : ℕ) :
    Measurable (fun z : Seed × (Fin m → Response d) => scan A S z T) := by
  have ho (n : ℕ) : Measurable (fun z : Seed × (Fin m → Response d) =>
      A.output n z.1 (historyPrefix n z.2)) :=
    (A.output_measurable n).comp
      (measurable_fst.prodMk ((prefix_measurable m n).comp measurable_snd))
  induction T with
  | zero => exact ho 0
  | succ T ih =>
    exact Measurable.ite
      (measurableSet_nat_choice (predicate S) (predicate_measurable S m) (index_measurable S m T))
      ih (ho (T + 1))

theorem scan_eq (A : Algorithm d Seed) (S : Rule d Seed) {m : ℕ}
    (z : Seed × (Fin m → Response d)) (T : ℕ) :
    scan A S z T = A.output (index S z T) z.1 (historyPrefix (index S z T) z.2) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    have he : index S z (T + 1) =
        if predicate S z (index S z T) then index S z T else T + 1 := rfl
    change (if predicate S z (index S z T) then scan A S z T else
      A.output (T + 1) z.1 (historyPrefix (T + 1) z.2)) = _
    by_cases h : predicate S z (index S z T)
    · have he' : index S z (T + 1) = index S z T := he.trans (if_pos h)
      rw [he']
      exact (if_pos h).trans ih
    · have he' : index S z (T + 1) = T + 1 := he.trans (if_neg h)
      rw [he']
      exact if_neg h

def compile (A : Algorithm d Seed) (S : Rule d Seed) (T : ℕ) : Algorithm d Seed where
  query := A.query
  output n seed h := scan A S (seed, h) (min T n)
  query_measurable := A.query_measurable
  output_measurable n := scan_measurable A S n (min T n)

theorem compile_transcript (A : Algorithm d Seed) (S : Rule d Seed) (T : ℕ)
    (f : Space d → ℝ) (seed : Seed) (n : ℕ) :
    transcript (compile A S T) f seed n = transcript A f seed n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [transcript, ih]; rfl

/-- The fixed-cap policy returns exactly the original output at its first
stopped history, with mandatory stopping at the cap if no predicate holds. -/
theorem terminal_output (A : Algorithm d Seed) (S : Rule d Seed) (T : ℕ)
    (f : Space d → ℝ) (seed : Seed) :
    let τ := index S (seed, transcript A f seed T) T
    (compile A S T).output T seed (transcript (compile A S T) f seed T) =
      A.output τ seed (transcript A f seed τ) := by
  dsimp only
  rw [compile_transcript]
  change scan A S (seed, transcript A f seed T) (min T T) = _
  rw [min_self, scan_eq, prefix_transcript A f seed (index_le S _ T)]

theorem first_stop_spec (A : Algorithm d Seed) (S : Rule d Seed) (T : ℕ)
    (f : Space d → ℝ) (seed : Seed) :
    let τ := index S (seed, transcript A f seed T) T
    τ ≤ T ∧ (S.stop τ seed (transcript A f seed τ) ∨ τ = T) ∧
      ∀ j < τ, ¬ S.stop j seed (transcript A f seed j) := by
  let z := (seed, transcript A f seed T)
  have hτ := index_le S z T
  refine ⟨hτ, ?_, ?_⟩
  · have h := firstIndex_found_or_last (predicate S z) T
    change predicate S z (index S z T) ∨ index S z T = T at h
    simpa only [predicate, z, prefix_transcript A f seed hτ] using h
  · intro j hj
    have h := firstIndex_min (predicate S z) T j hj
    simpa only [predicate, z, prefix_transcript A f seed ((le_of_lt hj).trans hτ)] using h

/-- The original rule's first stopping time. The value on a nonterminating
execution is immaterial under an almost-sure finite-cap assumption. -/
def stoppingTime (A : Algorithm d Seed) (S : Rule d Seed) (f : Space d → ℝ)
    (seed : Seed) : ℕ :=
  if h : ∃ n, S.stop n seed (transcript A f seed n) then Nat.find h else 0

def stoppedOutput (A : Algorithm d Seed) (S : Rule d Seed) (f : Space d → ℝ)
    (seed : Seed) : Space d :=
  A.output (stoppingTime A S f seed) seed (transcript A f seed (stoppingTime A S f seed))

theorem index_eq_stoppingTime (A : Algorithm d Seed) (S : Rule d Seed) (T : ℕ)
    (f : Space d → ℝ) (seed : Seed)
    (hcap : ∃ n ≤ T, S.stop n seed (transcript A f seed n)) :
    index S (seed, transcript A f seed T) T = stoppingTime A S f seed := by
  obtain ⟨n, hnT, hn⟩ := hcap
  have hex : ∃ n, S.stop n seed (transcript A f seed n) := ⟨n, hn⟩
  have hfind := Nat.find_spec hex
  have hfind_le : Nat.find hex ≤ T := (Nat.find_min' hex hn).trans hnT
  obtain ⟨hiT, hi, hmin⟩ := first_stop_spec A S T f seed
  have hie : index S (seed, transcript A f seed T) T = Nat.find hex := by
    apply le_antisymm
    · by_contra h
      exact hmin (Nat.find hex) (by omega) hfind
    · rcases hi with hi | hi
      · exact Nat.find_min' hex hi
      · omega
  simpa only [stoppingTime, dif_pos hex] using hie

/-- A cap that holds almost surely may fail on a different null set for each
fixed objective. Compiling the rule preserves the original stopped output
almost surely for that objective, without a uniform null-set assumption. -/
theorem terminal_output_ae (A : Algorithm d Seed) (S : Rule d Seed) (T : ℕ)
    (f : Space d → ℝ) (ν : Measure Seed)
    (hcap : ∀ᵐ seed ∂ν, ∃ n ≤ T, S.stop n seed (transcript A f seed n)) :
    (fun seed => (compile A S T).output T seed (transcript (compile A S T) f seed T))
      =ᵐ[ν] stoppedOutput A S f := by
  filter_upwards [hcap] with seed hseed
  rw [terminal_output, index_eq_stoppingTime A S T f seed hseed]
  rfl

theorem stoppedOutput_law (A : Algorithm d Seed) (S : Rule d Seed) (T : ℕ)
    (f : Space d → ℝ) (ν : Measure Seed)
    (hcap : ∀ᵐ seed ∂ν, ∃ n ≤ T, S.stop n seed (transcript A f seed n)) :
    ν.map (fun seed => (compile A S T).output T seed
      (transcript (compile A S T) f seed T)) = ν.map (stoppedOutput A S f) :=
  Measure.map_congr (terminal_output_ae A S T f ν hcap)

/-- In particular, the manuscript's success probability is unchanged by the
fixed-cap representation of a rule that stops by the cap almost surely. -/
theorem stoppedSuccess_probability (A : Algorithm d Seed) (S : Rule d Seed) (T : ℕ)
    (f : Space d → ℝ) (ε : ℝ) (ν : Measure Seed)
    (hcap : ∀ᵐ seed ∂ν, ∃ n ≤ T, S.stop n seed (transcript A f seed n)) :
    ν (Success (compile A S T) f ε T) =
      ν {seed | ‖gradient f (stoppedOutput A S f seed)‖ ≤ ε} := by
  apply measure_congr
  filter_upwards [terminal_output_ae A S T f ν hcap] with seed hseed
  change (‖gradient f ((compile A S T).output T seed
    (transcript (compile A S T) f seed T))‖ ≤ ε) = _
  rw [hseed]
  rfl

/-- A single measurable policy with an objective-wise almost-sure query cap
therefore supplies the fixed-cap witness used by the minimax model. -/
theorem randomizedCap_of_ae_stopping [StandardBorelSpace Seed]
    (p : ℕ) (A : Algorithm d Seed) (S : Rule d Seed) (T : ℕ) (ε : ℝ)
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (hcap : ∀ f : Space d → ℝ, InFunctionClass p f →
      ∀ᵐ seed ∂ν, ∃ n ≤ T, S.stop n seed (transcript A f seed n))
    (hsuccess : ∀ f : Space d → ℝ, InFunctionClass p f →
      (2 / 3 : ENNReal) ≤ ν {seed | ‖gradient f (stoppedOutput A S f seed)‖ ≤ ε}) :
    RandomizedCap p d ε T := by
  refine ⟨Seed, inferInstance, inferInstance, ν, inferInstance, compile A S T, ?_⟩
  intro f hf
  rw [stoppedSuccess_probability A S T f ε ν (hcap f hf)]
  exact hsuccess f hf

end MatchingBounds1005.Model.StoppingPolicy
