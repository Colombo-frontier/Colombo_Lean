import Bilevel.BorelAdaptiveExecution

/-! Exact original-oracle call counts for the absorbing finite execution.
On terminating paths the canonical stopping index equals the number of
actual calls, and capping at n uses exactly min(n,N) calls. -/
noncomputable section
open MeasureTheory
namespace Bilevel.BorelAdaptive

variable {S Q O Y I C : Type*} [MeasurableSpace S] [MeasurableSpace Q]
  [MeasurableSpace O] [MeasurableSpace Y] [MeasurableSpace I] [MeasurableSpace C]

def calls (A : Program S Q O Y) (response : I → Q → C → O)
    (i : I) (draws : ℕ → C) (initial : S) : ℕ → ℕ
  | 0 => 0
  | n+1 => calls A response i draws initial n+
      if A.halt (run A response i draws initial n) then 0 else 1

theorem calls_measurable (A : Program S Q O Y) (response : I → Q → C → O)
    (hr : Measurable (fun p : I × (Q × C) => response p.1 p.2.1 p.2.2)) (n : ℕ) :
    Measurable (fun p : Sample I S C => calls A response p.1 p.2.2 p.2.1 n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hh : MeasurableSet {p : Sample I S C | A.halt (run A response p.1 p.2.2 p.2.1 n)=true} :=
      (A.halt_measurable.comp (run_measurable A response hr n)) (measurableSet_singleton true)
    exact ih.add (measurable_const.ite hh measurable_const)

omit [MeasurableSpace I] [MeasurableSpace C] in
theorem calls_le (A : Program S Q O Y) (response : I → Q → C → O)
    (i : I) (draws : ℕ → C) (initial : S) (n : ℕ) : calls A response i draws initial n≤n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [calls]
    split_ifs <;> omega

omit [MeasurableSpace I] [MeasurableSpace C] in
theorem calls_eq_live (A : Program S Q O Y) (response : I → Q → C → O)
    (i : I) (draws : ℕ → C) (initial : S) (n : ℕ)
    (hlive : ∀ t<n,A.halt (run A response i draws initial t)=false) :
    calls A response i draws initial n=n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hp := ih (fun t ht => hlive t (by omega))
    simp only [calls,hp,hlive n (by omega),Bool.false_eq_true,if_false]

omit [MeasurableSpace I] [MeasurableSpace C] in
theorem calls_halted_add (A : Program S Q O Y) (response : I → Q → C → O)
    (i : I) (draws : ℕ → C) (initial : S) (n : ℕ)
    (hn : A.halt (run A response i draws initial n)=true) (k : ℕ) :
    calls A response i draws initial (n+k)=calls A response i draws initial n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.add_succ,calls,ih,run_halted_add A response i draws initial n hn k]
    simp only [hn,if_true,add_zero]

omit [MeasurableSpace I] [MeasurableSpace C] in
theorem calls_at_stop (A : Program S Q O Y) (response : I → Q → C → O)
    (p : Sample I S C) (hp : Terminated A response p) :
    calls A response p.1 p.2.2 p.2.1 (stopTime A response p)=stopTime A response p :=
  calls_eq_live A response p.1 p.2.2 p.2.1 _ (fun t ht => stopTime_first A response p hp t ht)

omit [MeasurableSpace I] [MeasurableSpace C] in
theorem calls_capped (A : Program S Q O Y) (response : I → Q → C → O)
    (p : Sample I S C) (hp : Terminated A response p) (n : ℕ) :
    calls A response p.1 p.2.2 p.2.1 n=min n (stopTime A response p) := by
  by_cases hn : n≤stopTime A response p
  · rw [Nat.min_eq_left hn]
    exact calls_eq_live A response p.1 p.2.2 p.2.1 n
      (fun t ht => stopTime_first A response p hp t (by omega))
  · have hle : stopTime A response p≤n := by omega
    have hh := calls_halted_add A response p.1 p.2.2 p.2.1 _ (stopTime_halted A response p hp)
      (n-stopTime A response p)
    rw [Nat.add_sub_of_le hle,calls_at_stop A response p hp] at hh
    simpa only [Nat.min_eq_right hle] using hh

theorem cappedOutput_agrees_ae (A : Program S Q O Y) (response : I → Q → C → O)
    (μ : Measure (Sample I S C)) (hterm : ∀ᵐ p ∂μ,Terminated A response p) (n : ℕ) :
    ∀ᵐ p ∂μ,stopTime A response p≤n → cappedOutput A response n p=stoppedOutput A response p := by
  filter_upwards [hterm] with p hp
  exact cappedOutput_agrees A response p hp n

end Bilevel.BorelAdaptive
