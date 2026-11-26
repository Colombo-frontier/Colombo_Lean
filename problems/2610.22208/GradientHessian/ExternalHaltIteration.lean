import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.Find

/-! A stop checked between transitions preserves the pending configuration.
These finite identities apply to both sides of the split at mark supply. -/

namespace GradientHessian.ExternalHaltIteration
variable {α : Type*}

def step (f : α → α) (halt : α → Bool) (x : α) : α := if halt x then x else f x

theorem stopped_fixed (f : α → α) (halt : α → Bool) (x : α) (hx : halt x=true) :
    step f halt x=x := by simp [step,hx]

theorem open_prefix (f : α → α) (halt : α → Bool) (x : α) (i N : ℕ)
    (hi : i≤N) (hN : halt ((step f halt)^[N] x)=false) :
    halt ((step f halt)^[i] x)=false := by
  cases hh : halt ((step f halt)^[i] x) with
  | false => rfl
  | true =>
      have hf := Function.iterate_fixed (stopped_fixed f halt _ hh) (N-i)
      have he : (step f halt)^[N] x=(step f halt)^[i] x := by
        calc
          (step f halt)^[N] x=(step f halt)^[N-i+i] x := by rw [Nat.sub_add_cancel hi]
          _=(step f halt)^[i] x := by rw [Function.iterate_add_apply,hf]
      rw [he,hh] at hN
      cases hN

theorem iterate_eq_of_open (f : α → α) (halt : α → Bool) (x : α) (N : ℕ)
    (hN : halt ((step f halt)^[N] x)=false) :
    (step f halt)^[N] x=f^[N] x := by
  induction N with
  | zero => rfl
  | succ N ih =>
      have hn := open_prefix f halt x N (N+1) (Nat.le_succ _) hN
      rw [Function.iterate_succ_apply',step,hn,if_neg Bool.false_ne_true,ih hn,
        Function.iterate_succ_apply']

theorem iterate_eq_before (f : α → α) (halt : α → Bool) (x : α) (N : ℕ)
    (hN : ∀ i<N,halt (f^[i] x)=false) :
    (step f halt)^[N] x=f^[N] x := by
  induction N with
  | zero => rfl
  | succ N ih =>
      have hn := ih (fun i hi => hN i (Nat.lt_trans hi (Nat.lt_succ_self _)))
      rw [Function.iterate_succ_apply',hn,step,hN N (Nat.lt_succ_self _),if_neg Bool.false_ne_true,
        Function.iterate_succ_apply']

theorem first_stop (f : α → α) (halt : α → Bool) (x : α) (N : ℕ)
    (hN : halt (f^[N] x)=true) :
    ∃ k≤N,halt (f^[k] x)=true ∧ (∀ i<k,halt (f^[i] x)=false) ∧
      (step f halt)^[k] x=f^[k] x ∧
      ∀ m,k≤m → (step f halt)^[m] x=f^[k] x := by
  have hex : ∃ k,halt (f^[k] x)=true := ⟨N,hN⟩
  let k := Nat.find hex
  have hk : halt (f^[k] x)=true := Nat.find_spec hex
  have hpre : ∀ i<k,halt (f^[i] x)=false := by
    intro i hi
    cases hh : halt (f^[i] x) with
    | false => rfl
    | true => exact False.elim ((Nat.find_min hex hi) hh)
  have he := iterate_eq_before f halt x k hpre
  refine ⟨k,Nat.find_min' hex hN,hk,hpre,he,?_⟩
  intro m hm
  calc
    (step f halt)^[m] x=(step f halt)^[m-k+k] x := by rw [Nat.sub_add_cancel hm]
    _=(step f halt)^[m-k] (f^[k] x) := by rw [Function.iterate_add_apply,he]
    _=f^[k] x := Function.iterate_fixed (stopped_fixed f halt _ hk) _

end GradientHessian.ExternalHaltIteration
