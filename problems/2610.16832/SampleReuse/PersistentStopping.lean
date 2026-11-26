import SampleReuse.PersistentHandleLaw
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

open SecondOrder MeasureTheory
open scoped Classical ENNReal
namespace SampleReuse
noncomputable section

def persistentStopScan {O : Type*} (stop : ℕ → Bool) (output : ℕ → O) : ℕ → Bool × O
  | 0 => (stop 0,output 0)
  | n+1 => let old := persistentStopScan stop output n
    if old.1 = true then old else (stop (n+1),output (n+1))

theorem persistentStopScan_no_stop {O : Type*} (stop : ℕ → Bool) (output : ℕ → O)
    (N : ℕ) (hs : ∀ k ≤ N, stop k = false) :
    persistentStopScan stop output N = (false,output N) := by
  induction N with
  | zero => exact Prod.ext (hs 0 le_rfl) rfl
  | succ N ih =>
    rw [persistentStopScan,ih (fun k hk => hs k (by omega))]
    simp only [Bool.false_eq_true,↓reduceIte,hs (N+1) le_rfl]

theorem persistentStopScan_first {O : Type*} (stop : ℕ → Bool) (output : ℕ → O)
    (k N : ℕ) (hkN : k ≤ N) (hk : stop k = true) (hs : ∀ j < k, stop j = false) :
    persistentStopScan stop output N = (true,output k) := by
  induction N with
  | zero => have he : k = 0 := by omega
            subst k
            exact Prod.ext hk rfl
  | succ N ih =>
    by_cases hN : k ≤ N
    · rw [persistentStopScan,ih hN]
      simp only [↓reduceIte]
    · have he : k = N+1 := by omega
      subst k
      rw [persistentStopScan,persistentStopScan_no_stop stop output N (fun j hj => hs j (by omega))]
      simp only [Bool.false_eq_true,↓reduceIte,hk]

structure PersistentStoppingAlgorithm (Q H Y O S : Type*) extends OracleAlgorithm (Q × H) Y O S where
  stop : ℕ → S → Bool

namespace PersistentStoppingAlgorithm
variable {Q H Y O S Z : Type*}

def state (P : PersistentStoppingAlgorithm Q H Y O S) (reply : Q → Z → Y)
    (tape : ℕ → Z) (n : ℕ) : S := (lazyPersistentRun P.toQueryPolicy reply tape n).1

def stopOnRun (P : PersistentStoppingAlgorithm Q H Y O S) (reply : Q → Z → Y)
    (tape : ℕ → Z) (n : ℕ) : Bool := P.stop n (P.state reply tape n)

def outputAt (P : PersistentStoppingAlgorithm Q H Y O S) (reply : Q → Z → Y)
    (tape : ℕ → Z) (n : ℕ) : O := P.output n (P.state reply tape n)

/-- A fixed-cap policy retains the first stopped output while continuing
dummy execution to the cap. It reads only the actual oracle replies. -/
def cap (P : PersistentStoppingAlgorithm Q H Y O S) : OracleAlgorithm (Q × H) Y O (S × (Bool × O)) where
  initial := (P.initial,(P.stop 0 P.initial,P.output 0 P.initial))
  query n s := P.query n s.1
  update n s y := let next := P.update n s.1 y
    (next,if s.2.1 = true then s.2 else (P.stop (n+1) next,P.output (n+1) next))
  output _ s := s.2.2

theorem cap_run (P : PersistentStoppingAlgorithm Q H Y O S) (reply : Q → Z → Y)
    (tape : ℕ → Z) : ∀ n,
    lazyPersistentRun P.cap.toQueryPolicy reply tape n =
      ((P.state reply tape n,persistentStopScan (P.stopOnRun reply tape) (P.outputAt reply tape) n),
        (lazyPersistentRun P.toQueryPolicy reply tape n).2) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [lazyPersistentRun,ih]
    rfl

def Halts (P : PersistentStoppingAlgorithm Q H Y O S) (reply : Q → Z → Y) (tape : ℕ → Z) : Prop :=
  ∃ n, P.stopOnRun reply tape n = true

def cost (P : PersistentStoppingAlgorithm Q H Y O S) (reply : Q → Z → Y) (tape : ℕ → Z) : ℕ :=
  if hh : P.Halts reply tape then Nat.find hh else 0

def outputFor (P : PersistentStoppingAlgorithm Q H Y O S) (reply : Q → Z → Y) (tape : ℕ → Z) : O :=
  P.outputAt reply tape (P.cost reply tape)

theorem cap_agrees (P : PersistentStoppingAlgorithm Q H Y O S) (reply : Q → Z → Y)
    (tape : ℕ → Z) (hh : P.Halts reply tape) (N : ℕ) (hN : P.cost reply tape ≤ N) :
    P.cap.output N (lazyPersistentRun P.cap.toQueryPolicy reply tape N).1 = P.outputFor reply tape := by
  have hc : P.cost reply tape = Nat.find hh := dif_pos hh
  have hbefore : ∀ k < Nat.find hh, P.stopOnRun reply tape k = false := by
    intro k hk
    cases he : P.stopOnRun reply tape k
    · rfl
    · exact False.elim (Nat.find_min hh hk he)
  rw [cap_run]
  change (persistentStopScan (P.stopOnRun reply tape) (P.outputAt reply tape) N).2 = _
  rw [persistentStopScan_first _ _ (Nat.find hh) N (by simpa only [hc] using hN)
    (Nat.find_spec hh) hbefore]
  change P.outputAt reply tape (Nat.find hh) = P.outputAt reply tape (P.cost reply tape)
  rw [hc]

def NoStopBefore (P : PersistentStoppingAlgorithm Q H Y O S) (reply : Q → Z → Y)
    (tape : ℕ → Z) (n : ℕ) : Prop := ∀ k < n, P.stopOnRun reply tape k = false

/-- The actual extended count is infinite on nonhalting runs. -/
def extendedCost (P : PersistentStoppingAlgorithm Q H Y O S) (reply : Q → Z → Y)
    (tape : ℕ → Z) : ℝ≥0∞ :=
  ⨆ n : ℕ, if P.NoStopBefore reply tape n then (n : ℝ≥0∞) else 0

theorem extendedCost_eq_cost (P : PersistentStoppingAlgorithm Q H Y O S) (reply : Q → Z → Y)
    (tape : ℕ → Z) (hh : P.Halts reply tape) :
    P.extendedCost reply tape = (P.cost reply tape : ℝ≥0∞) := by
  have hc : P.cost reply tape = Nat.find hh := dif_pos hh
  have hb : P.NoStopBefore reply tape (Nat.find hh) := by
    intro k hk
    cases he : P.stopOnRun reply tape k
    · rfl
    · exact False.elim (Nat.find_min hh hk he)
  rw [hc]
  apply le_antisymm
  · apply iSup_le
    intro n
    by_cases hn : P.NoStopBefore reply tape n
    · rw [if_pos hn]
      have hnc : n ≤ Nat.find hh := by
        by_contra h
        have hs := hn (Nat.find hh) (by omega)
        rw [Nat.find_spec hh] at hs
        contradiction
      exact_mod_cast hnc
    · rw [if_neg hn]; exact zero_le _
  · exact le_iSup_of_le (Nat.find hh) (by rw [if_pos hb])

theorem extendedCost_eq_top (P : PersistentStoppingAlgorithm Q H Y O S) (reply : Q → Z → Y)
    (tape : ℕ → Z) (hh : ¬P.Halts reply tape) : P.extendedCost reply tape = ∞ := by
  have hb (n : ℕ) : P.NoStopBefore reply tape n := by
    intro k _
    cases he : P.stopOnRun reply tape k
    · rfl
    · exact False.elim (hh ⟨k,he⟩)
  simp only [extendedCost,if_pos (hb _),ENNReal.iSup_natCast]

end PersistentStoppingAlgorithm
end
end SampleReuse
