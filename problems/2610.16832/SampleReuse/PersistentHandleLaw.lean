import SampleReuse.PersistentHandleHistory

/-! The entire actual rich-reply program has the same law after finite-slot
normalization. The history here records full latent samples only for the
proof; the normalized algorithm receives only the original oracle reply. -/

open SecondOrder
open scoped Classical
namespace SampleReuse
noncomputable section
variable {Q H Y S Z : Type}

def sampleHistoryState (P : QueryPolicy (Q × H) Y S) (reply : Q → Z → Y) :
    (n : ℕ) → FiniteHistory Unit Z n → S
  | 0, _ => P.initial
  | n+1,h => let s := sampleHistoryState P reply n h.1
    P.update n s (reply (P.query n s).1 h.2)

def sampleHistoryHandle (P : QueryPolicy (Q × H) Y S) (reply : Q → Z → Y)
    (n : ℕ) (h : FiniteHistory Unit Z n) : H :=
  (P.query n (sampleHistoryState P reply n h)).2

theorem normalized_sampleHistoryState (N : ℕ) (P : QueryPolicy (Q × H) Y S)
    (reply : Q → Z → Y) : ∀ n h,
    sampleHistoryState (normalizePersistentPolicy N P) reply n h =
      (sampleHistoryState P reply n h, queriedLabels (sampleHistoryHandle P reply) n h) := by
  intro n
  induction n with
  | zero => intro h; rfl
  | succ n ih =>
    intro h
    simp only [sampleHistoryState]
    rw [ih]
    rfl

theorem normalized_sampleHistoryHandle (N : ℕ) (P : QueryPolicy (Q × H) Y S)
    (reply : Q → Z → Y) :
    sampleHistoryHandle (normalizePersistentPolicy N P) reply =
      normalizeHandleQuery N (sampleHistoryHandle P reply) := by
  funext n h
  change ((normalizePersistentPolicy N P).query n
    (sampleHistoryState (normalizePersistentPolicy N P) reply n h)).2 = _
  rw [normalized_sampleHistoryState]
  rfl

theorem persistentQueryRun_history (P : QueryPolicy (Q × H) Y S)
    (reply : Q → Z → Y) (table : H → Z) : ∀ n,
    persistentQueryRun P reply table n =
      sampleHistoryState P reply n (tableHistory (sampleHistoryHandle P reply) () table n) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [persistentQueryRun,tableHistory,sampleHistoryState,ih,sampleHistoryHandle]

def lazyPersistentStateLaw (P : QueryPolicy (Q × H) Y S) (reply : Q → Z → Y)
    (p : PMF Z) (N : ℕ) : PMF S :=
  (lazyDisclosurePMF (sampleHistoryHandle P reply) (fun _ => p) () N).map
    (sampleHistoryState P reply N)

/-- A complete law equality for every original state, not merely a scalar
statistic. Handle labels may have arbitrary cardinality. -/
theorem normalized_persistent_state_law [Fintype Z] (N : ℕ)
    (P : QueryPolicy (Q × H) Y S) (reply : Q → Z → Y) (p : PMF Z) :
    (finitePiPMF (fun _ : Fin (N+1) => p)).map
      (fun table => (persistentQueryRun (normalizePersistentPolicy N P) reply table N).1) =
      lazyPersistentStateLaw P reply p N := by
  have he (table : Fin (N+1) → Z) :
      (persistentQueryRun (normalizePersistentPolicy N P) reply table N).1 =
        sampleHistoryState P reply N
          (tableHistory (normalizeHandleQuery N (sampleHistoryHandle P reply)) () table N) := by
    rw [persistentQueryRun_history,normalized_sampleHistoryState,normalized_sampleHistoryHandle]
  simp_rw [he]
  have hm := PMF.map_comp
    (fun table => tableHistory (normalizeHandleQuery N (sampleHistoryHandle P reply)) () table N)
    (finitePiPMF (fun _ : Fin (N+1) => p))
    (sampleHistoryState P reply N)
  simp only [Function.comp_def] at hm
  rw [← hm]
  change (preallocatedHistoryPMF (normalizeHandleQuery N (sampleHistoryHandle P reply))
    (fun _ => p) () N).map _ = _
  rw [preallocatedHistoryPMF_eq_lazy,normalized_lazy_law N _ p () N le_rfl]
  rfl

def lazyPersistentOutputLaw {O : Type} (P : OracleAlgorithm (Q × H) Y O S)
    (reply : Q → Z → Y) (p : PMF Z) (N : ℕ) : PMF O :=
  (lazyPersistentStateLaw P.toQueryPolicy reply p N).map (P.output N)

theorem normalized_persistent_output_law {O : Type} [Fintype Z] (N : ℕ)
    (P : OracleAlgorithm (Q × H) Y O S) (reply : Q → Z → Y) (p : PMF Z) :
    (finitePiPMF (fun _ : Fin (N+1) => p)).map
      (fun table => (normalizePersistentAlgorithm N P).output N
        (persistentQueryRun (normalizePersistentAlgorithm N P).toQueryPolicy reply table N)) =
      lazyPersistentOutputLaw P reply p N := by
  change (finitePiPMF (fun _ : Fin (N+1) => p)).map
    (fun table => P.output N (persistentQueryRun (normalizePersistentPolicy N P.toQueryPolicy)
      reply table N).1) = _
  have hm := PMF.map_comp
    (fun table => (persistentQueryRun (normalizePersistentPolicy N P.toQueryPolicy) reply table N).1)
    (finitePiPMF (fun _ : Fin (N+1) => p))
    (P.output N)
  simp only [Function.comp_def] at hm
  rw [← hm,normalized_persistent_state_law]
  rfl

/-- When the original label set is finite, the operational lazy law agrees
with its usual immutable iid product table. -/
theorem persistent_state_eq_lazy [Fintype H] [Fintype Z]
    (P : QueryPolicy (Q × H) Y S) (reply : Q → Z → Y) (p : PMF Z) (N : ℕ) :
    (finitePiPMF (fun _ : H => p)).map (fun table => persistentQueryRun P reply table N) =
      lazyPersistentStateLaw P reply p N := by
  simp_rw [persistentQueryRun_history]
  have hm := PMF.map_comp (fun table => tableHistory (sampleHistoryHandle P reply) () table N)
    (finitePiPMF (fun _ : H => p)) (sampleHistoryState P reply N)
  simp only [Function.comp_def] at hm
  rw [← hm]
  change (preallocatedHistoryPMF (sampleHistoryHandle P reply) (fun _ => p) () N).map _ = _
  rw [preallocatedHistoryPMF_eq_lazy]
  rfl

end
end SampleReuse
