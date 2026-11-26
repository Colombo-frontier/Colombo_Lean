import SecondOrder.OracleAlgorithm
import Mathlib.Data.List.Basic

/-! Handle labels are retained as private algorithm data. Only evaluated
labels receive sample slots. Repeated evaluations return to the first slot. -/

open SecondOrder
open scoped Classical
namespace SampleReuse
noncomputable section

def handleSlot {H : Type*} (N : ℕ) (labels : List H) (h : H) : Fin (N+1) :=
  ⟨min (labels.idxOf h) N, by omega⟩

theorem handleSlot_val {H : Type*} (N : ℕ) (labels : List H) (h : H)
    (hlen : labels.length ≤ N) : (handleSlot N labels h).val = labels.idxOf h := by
  exact min_eq_left (List.idxOf_le_length.trans hlen)

theorem handleSlot_fresh {H : Type*} (N : ℕ) (labels : List H) (h : H)
    (hlen : labels.length ≤ N) (hfresh : h ∉ labels) :
    (handleSlot N labels h).val = labels.length := by
  rw [handleSlot_val N labels h hlen, List.idxOf_of_not_mem hfresh]

theorem handleSlot_reused {H : Type*} (N : ℕ) (labels extra : List H) (h : H)
    (hseen : h ∈ labels) : handleSlot N (labels ++ extra) h = handleSlot N labels h := by
  simp only [handleSlot, List.idxOf_append_of_mem hseen]

theorem handleSlot_append_self {H : Type*} (N : ℕ) (labels : List H) (h : H) :
    handleSlot N (labels ++ [h]) h = handleSlot N labels h := by
  by_cases hh : h ∈ labels
  · exact handleSlot_reused N labels [h] h hh
  · simp only [handleSlot,List.idxOf_append_of_not_mem hh,List.idxOf_of_not_mem hh]
    simp

theorem handleSlot_eq_iff {H : Type*} (N : ℕ) (labels : List H) (h k : H)
    (hlen : labels.length ≤ N) (hh : h ∈ labels) :
    handleSlot N labels h = handleSlot N labels k ↔ h = k := by
  constructor
  · intro he
    have hi := congrArg Fin.val he
    simp only [handleSlot_val N labels _ hlen] at hi
    have hk : k ∈ labels := List.idxOf_lt_length_iff.mp
      (hi ▸ List.idxOf_lt_length_iff.mpr hh)
    exact (List.idxOf_inj hh hk).mp hi
  · rintro rfl; rfl

def persistentQueryRun {Q H Y S Z : Type*} (P : QueryPolicy (Q × H) Y S)
    (reply : Q → Z → Y) (table : H → Z) : ℕ → S
  | 0 => P.initial
  | n+1 => let s := persistentQueryRun P reply table n
    let q := P.query n s
    P.update n s (reply q.1 (table q.2))

/-- A tape cell is reserved by the first actual evaluation of a label.
Cells corresponding to repeated evaluations are left unread. -/
def lazyPersistentRun {Q H Y S Z : Type*} (P : QueryPolicy (Q × H) Y S)
    (reply : Q → Z → Y) (tape : ℕ → Z) : ℕ → S × List H
  | 0 => (P.initial,[])
  | n+1 => let s := lazyPersistentRun P reply tape n
    let q := P.query n s.1
    (P.update n s.1 (reply q.1 (tape (s.2.idxOf q.2))), s.2 ++ [q.2])

theorem lazyPersistentRun_length {Q H Y S Z : Type*} (P : QueryPolicy (Q × H) Y S)
    (reply : Q → Z → Y) (tape : ℕ → Z) (n : ℕ) :
    (lazyPersistentRun P reply tape n).2.length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [lazyPersistentRun,List.length_append,List.length_singleton,ih]

def normalizePersistentPolicy {Q H Y S : Type*} (N : ℕ) (P : QueryPolicy (Q × H) Y S) :
    QueryPolicy (Q × Fin (N+1)) Y (S × List H) where
  initial := (P.initial,[])
  query n s := let q := P.query n s.1; (q.1,handleSlot N s.2 q.2)
  update n s y := (P.update n s.1 y,s.2 ++ [(P.query n s.1).2])

def normalizePersistentAlgorithm {Q H Y O S : Type*} (N : ℕ)
    (P : OracleAlgorithm (Q × H) Y O S) :
    OracleAlgorithm (Q × Fin (N+1)) Y O (S × List H) where
  toQueryPolicy := normalizePersistentPolicy N P.toQueryPolicy
  output n s := P.output n s.1

/-- Every reply and the complete original state agree through the cap.
No finiteness, countability, or cardinality bound on labels is assumed. -/
theorem normalizePersistentPolicy_run {Q H Y S Z : Type*} (N : ℕ)
    (P : QueryPolicy (Q × H) Y S) (reply : Q → Z → Y)
    (table : Fin (N+1) → Z) (tape : ℕ → Z)
    (htape : ∀ i : Fin (N+1), tape i.val = table i) :
    ∀ n, n ≤ N → persistentQueryRun (normalizePersistentPolicy N P) reply table n =
      lazyPersistentRun P reply tape n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    simp only [persistentQueryRun, lazyPersistentRun]
    rw [ih (by omega)]
    simp only [normalizePersistentPolicy]
    have hlen : (lazyPersistentRun P reply tape n).2.length ≤ N := by
      rw [lazyPersistentRun_length]; omega
    have ht := htape (handleSlot N (lazyPersistentRun P reply tape n).2
      (P.query n (lazyPersistentRun P reply tape n).1).2)
    rw [handleSlot_val N _ _ hlen] at ht
    rw [ht]

theorem normalizePersistentAlgorithm_output {Q H Y O S Z : Type*} (N : ℕ)
    (P : OracleAlgorithm (Q × H) Y O S) (reply : Q → Z → Y)
    (table : Fin (N+1) → Z) (tape : ℕ → Z)
    (htape : ∀ i : Fin (N+1), tape i.val = table i) :
    (normalizePersistentAlgorithm N P).output N
      (persistentQueryRun (normalizePersistentAlgorithm N P).toQueryPolicy reply table N) =
      P.output N (lazyPersistentRun P.toQueryPolicy reply tape N).1 := by
  change P.output N (persistentQueryRun (normalizePersistentPolicy N P.toQueryPolicy)
    reply table N).1 = _
  rw [normalizePersistentPolicy_run N P.toQueryPolicy reply table tape htape N le_rfl]

end
end SampleReuse
