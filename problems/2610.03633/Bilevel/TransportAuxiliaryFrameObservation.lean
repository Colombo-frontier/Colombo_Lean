import Bilevel.TransportAuxiliaryFrameReplay
import Bilevel.SourceFrameKnownSpace

/-! The selected-frame observation space has the exact deterministic old
prefix at every query batch. Both that batch and the arbitrary terminal
output belong to the spaces controlled by the actual raw-genie run. -/
noncomputable section
namespace Bilevel.TransportAuxiliaryFrame
open EuclideanGaussian ProjectionPosterior TransportControllerMachine
set_option autoImplicit false
universe u v
variable {C : Type u} {S : Type v} [MeasurableSpace C] [MeasurableSpace S]
  {k T D B : ℕ}

def knownPrefix (P : Schedule k T) (t : ℕ) (i : Fin k) : Set (Fin (T+1)) :=
  {a | a.val < P.count t i}

theorem selected_step_known (P : Schedule k T) (A : Driver C S k T D B) (i : Fin k)
    (t : ℕ) (s : SourceFrameActions.State (SelectedMemory C S k T D) D (T+1))
    (U : Frame D (T+1)) (hs : s.2.2=knownPrefix P t i) :
    (SourceFrameActions.observeStep (selectedRules P A i) t s U).2.2=knownPrefix P (t+1) i := by
  by_cases h : P.count t i < P.count (t+1) i
  · have hb : P.count t i < T+1 := lt_of_lt_of_le h (P.bound (t+1) i)
    have hr : (selectedRules P A i).request t s.1 = true := by
      simpa only [selectedRules,request,decide_eq_true_eq] using h
    have he : P.count (t+1) i = P.count t i+1 := by
      have hh := P.step t i
      omega
    simp only [SourceFrameActions.observeStep,hr,if_true]
    simp only [selectedRules,column,dif_pos hb,hs,knownPrefix,he]
    ext a
    simp only [Set.mem_insert_iff,Set.mem_setOf_eq]
    constructor
    · intro ha
      rcases ha with ha | ha
      · subst a; simp
      · omega
    · intro ha
      by_cases heq : a.val=P.count t i
      · exact Or.inl (Fin.ext heq)
      · exact Or.inr (by omega)
  · have he : P.count (t+1) i = P.count t i := le_antisymm (le_of_not_gt h) (P.mono t i)
    have hr : ¬(selectedRules P A i).request t s.1 = true := by
      simpa only [selectedRules,request,decide_eq_true_eq] using h
    simp only [SourceFrameActions.observeStep,if_neg hr,hs,knownPrefix,he]

theorem selected_batch_known (P : Schedule k T) (A : Driver C S k T D B)
    (i : Fin k) (hB : 0 < B) : ∀ n t
    (s : SourceFrameActions.State (SelectedMemory C S k T D) D (T+1))
    (U : Frame D (T+1)), s.2.2=knownPrefix P t i →
    (SourceFrameActions.observeRun (selectedBatchRules P A i hB) (n*B) (t*B) s U).2.2 =
      knownPrefix P (t+n) i := by
  intro n
  induction n with
  | zero => intro t s U h; simpa only [Nat.zero_mul,SourceFrameActions.observeRun,Nat.add_zero] using h
  | succ n ih =>
    intro t s U h
    have hknown := (SourceFrameActions.batch_known_one (selectedRules P A i) hB
      (selectedQueries A) (selectedQueries_measurable A) t s U).trans
        (selected_step_known P A i t s U h)
    have he : (n+1)*B=B+n*B := by ring
    have ht : t*B+B=(t+1)*B := by ring
    rw [he,SourceFrameActions.observeRun_add,ht]
    have hh := ih (t+1) (SourceFrameActions.observeRun (selectedBatchRules P A i hB) B (t*B) s U) U hknown
    have hn : (t+1)+n=t+(n+1) := by omega
    simpa only [hn] using hh

def observation (P : Schedule k T) (A : Driver C S k T D B) (i : Fin k) (hB : 0 < B)
    (n : ℕ) (V U : Columns k T D) (s : State C S k T D) :=
  SourceFrameActions.observeRun (selectedBatchRules P A i hB) (n*B) 0 ((V,s),(⊥,∅)) (U i)

def preSpace (P : Schedule k T) (A : Driver C S k T D B) (i : Fin k) (hB : 0 < B)
    (n : ℕ) (V U : Columns k T D) (s : State C S k T D) : Submodule ℝ (Space D) :=
  SourceFrameActions.batchPreSpace (selectedRules P A i) hB
    (selectedQueries A) (selectedQueries_measurable A) n (observation P A i hB n V U s) (U i)

def terminalSpace (P : Schedule k T) (A : Driver C S k T D B) (i : Fin k) (hB : 0 < B)
    (n : ℕ) (V U : Columns k T D) (s : State C S k T D) : Submodule ℝ (Space D) :=
  (SourceFrameActions.finishObservation (selectedBatchRules P A i hB)
    (observation P A i hB n V U s)).2.1

theorem observation_memory (P : Schedule k T) (A : Driver C S k T D B) (i : Fin k) (hB : 0 < B)
    (n : ℕ) (V U : Columns k T D) (hVU : ∀ j, j ≠ i → V j = U j) (s : State C S k T D) :
    (observation P A i hB n V U s).1=(V,run P A n 0 s U) := by
  rw [observation,SourceFrameActions.observeRun_memory]
  simpa only [Nat.zero_mul] using selected_batch_run_actual P A i hB n 0 V U hVU s

theorem observation_known (P : Schedule k T) (A : Driver C S k T D B) (i : Fin k) (hB : 0 < B)
    (n : ℕ) (V U : Columns k T D) (s : State C S k T D) :
    (observation P A i hB n V U s).2.2=knownPrefix P n i := by
  have hz : (∅ : Set (Fin (T+1)))=knownPrefix P 0 i := by simp [knownPrefix,P.zero]
  simpa only [observation,Nat.zero_mul,Nat.zero_add] using
    selected_batch_known P A i hB n 0 ((V,s),(⊥,∅)) (U i) hz

theorem query_mem_preSpace (P : Schedule k T) (A : Driver C S k T D B) (i : Fin k) (hB : 0 < B)
    (n : ℕ) (V U : Columns k T D) (hVU : ∀ j, j ≠ i → V j = U j)
    (s : State C S k T D) (b : Fin B) :
    A.queries n (run P A n 0 s U) b ∈ preSpace P A i hB n V U s := by
  have hm := SourceFrameActions.batch_pre_query_mem (selectedRules P A i) hB
    (selectedQueries A) (selectedQueries_measurable A) n (observation P A i hB n V U s) (U i) b
  rw [observation_memory P A i hB n V U hVU s] at hm
  exact hm

theorem output_mem_terminalSpace (P : Schedule k T) (A : Driver C S k T D B) (i : Fin k) (hB : 0 < B)
    (n : ℕ) (V U : Columns k T D) (hVU : ∀ j, j ≠ i → V j = U j) (s : State C S k T D) :
    A.output (run P A n 0 s U) ∈ terminalSpace P A i hB n V U s := by
  unfold terminalSpace SourceFrameActions.finishObservation
  apply Submodule.mem_sup_right
  apply Submodule.subset_span
  rw [Set.mem_singleton_iff]
  rw [observation_memory P A i hB n V U hVU s]
  rfl

def ProjectionGood (P : Schedule k T) (A : Driver C S k T D B) (i : Fin k) (hB : 0 < B)
    (N : ℕ) (V U : Columns k T D) (s : State C S k T D) (cap : ℝ) : Prop :=
  (∀ j < N, GenieProtocol.BoundedEnergy (preSpace P A i hB j V U s) (knownPrefix P j i) (U i) cap) ∧
    GenieProtocol.BoundedEnergy (terminalSpace P A i hB N V U s) (knownPrefix P N i) (U i) cap

theorem sourceObserved_projectionGood (P : Schedule k T) (A : Driver C S k T D B)
    (i : Fin k) (hB : 0 < B) (N : ℕ) (V U : Columns k T D) (s : State C S k T D) (cap : ℝ)
    (h : SourceFrameActions.SourceObserved (selectedBatchRules P A i hB) cap (N*B) 0
      ((V,s),(⊥,∅)) (U i)) : ProjectionGood P A i hB N V U s cap := by
  constructor
  · intro j hj
    have hh := SourceFrameActions.batch_pre_energy_at_call (selectedRules P A i) hB
      (selectedQueries A) (selectedQueries_measurable A) N j hj ((V,s),(⊥,∅)) (U i) cap h
    change GenieProtocol.BoundedEnergy (preSpace P A i hB j V U s)
      (observation P A i hB j V U s).2.2 (U i) cap at hh
    rw [observation_known] at hh
    exact hh
  · have hh := SourceFrameActions.source_observed_final (selectedBatchRules P A i hB)
      cap (N*B) 0 ((V,s),(⊥,∅)) (U i) h
    change GenieProtocol.BoundedEnergy (terminalSpace P A i hB N V U s)
      (observation P A i hB N V U s).2.2 (U i) cap at hh
    rw [observation_known] at hh
    exact hh

end Bilevel.TransportAuxiliaryFrame
