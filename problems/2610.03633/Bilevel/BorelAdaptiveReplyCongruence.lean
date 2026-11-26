import Bilevel.BorelAdaptiveExtendedCalls

/-! The same original reply has the same entire execution, including arbitrary
stopping and infinite cost, regardless of the bookkeeping type of the hidden
instance. No hidden instance is passed to the program. -/
noncomputable section
open MeasureTheory
namespace Bilevel.BorelAdaptive
set_option autoImplicit false
variable {S Q O Y I I' C Private : Type*}
  [MeasurableSpace S] [MeasurableSpace Q] [MeasurableSpace O] [MeasurableSpace Y]

theorem run_reply_congr (A : Program S Q O Y)
    (r : I → Q → C → O) (r' : I' → Q → C → O) (i : I) (i' : I')
    (h : ∀ q c,r i q c=r' i' q c) (draws : ℕ → C) (s : S) (n : ℕ) :
    run A r i draws s n=run A r' i' draws s n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [run,step,ih,h]

theorem stopTime_reply_congr (A : Program S Q O Y)
    (r : I → Q → C → O) (r' : I' → Q → C → O) (i : I) (i' : I')
    (h : ∀ q c,r i q c=r' i' q c) (draws : ℕ → C) (s : S) :
    stopTime A r (i,(s,draws))=stopTime A r' (i',(s,draws)) := by
  have ht : Terminated A r (i,(s,draws)) ↔ Terminated A r' (i',(s,draws)) := by
    apply exists_congr
    intro n
    rw [run_reply_congr A r r' i i' h draws s n]
  by_cases hp : Terminated A r (i,(s,draws))
  · have hp' := ht.mp hp
    simp only [stopTime,dif_pos hp,dif_pos hp']
    apply Nat.le_antisymm
    · apply Nat.find_min' hp
      change A.halt (run A r i draws s (Nat.find hp'))=true
      rw [run_reply_congr A r r' i i' h]
      exact Nat.find_spec hp'
    · apply Nat.find_min' hp'
      change A.halt (run A r' i' draws s (Nat.find hp))=true
      rw [← run_reply_congr A r r' i i' h]
      exact Nat.find_spec hp
  · simp only [stopTime,dif_neg hp,dif_neg (mt ht.mpr hp)]

theorem seededStopped_reply_congr (A : Program S Q O Y)
    (r : I → Q → C → O) (r' : I' → Q → C → O) (i : I) (i' : I')
    (h : ∀ q c,r i q c=r' i' q c) (start : Private → S) (z : Private × (ℕ → C)) :
    (seededStopped A r start (i,z)).2=(seededStopped A r' start (i',z)).2 := by
  change A.output (run A r i z.2 (start z.1) (stopTime A r (i,(start z.1,z.2))))=
    A.output (run A r' i' z.2 (start z.1) (stopTime A r' (i',(start z.1,z.2))))
  rw [stopTime_reply_congr A r r' i i' h,run_reply_congr A r r' i i' h]

theorem seededCalls_reply_congr (A : Program S Q O Y)
    (r : I → Q → C → O) (r' : I' → Q → C → O) (i : I) (i' : I')
    (h : ∀ q c,r i q c=r' i' q c) (start : Private → S) (z : Private × (ℕ → C)) :
    seededCalls A r start (i,z)=seededCalls A r' start (i',z) := by
  have he : run A r i z.2 (start z.1)=run A r' i' z.2 (start z.1) :=
    funext (run_reply_congr A r r' i i' h z.2 (start z.1))
  simp only [seededCalls,seedInput,totalCalls,Terminated,he,
    stopTime_reply_congr A r r' i i' h]
  rw [he]

end Bilevel.BorelAdaptive
