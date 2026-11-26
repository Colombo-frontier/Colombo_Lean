import Bilevel.TransportAuxiliaryFrameStore

/-! Actual Borel adaptive execution on the finite auxiliary prefix store.
The immutable context may contain the entire network and private draws;
the mutable memory sees auxiliary columns only through the store. -/
noncomputable section
open MeasureTheory
universe u v
namespace Bilevel.TransportAuxiliaryFrame
open EuclideanGaussian
set_option autoImplicit false

abbrev State (C : Type u) (S : Type v) (k T D : ℕ) := C × (S × Store k T D)

structure Driver (C : Type u) (S : Type v) [MeasurableSpace C] [MeasurableSpace S]
    (k T D B : ℕ) where
  queries : ℕ → State C S k T D → Fin B → Space D
  queries_measurable : ∀ t b, Measurable (fun s => queries t s b)
  respond : ℕ → State C S k T D × Store k T D → S
  respond_measurable : ∀ t, Measurable (respond t)
  output : State C S k T D → Space D
  output_measurable : Measurable output

variable {C : Type u} {S : Type v} [MeasurableSpace C] [MeasurableSpace S]
  {k T D B : ℕ}

def step (P : Schedule k T) (A : Driver C S k T D B) (t : ℕ)
    (s : State C S k T D) (U : Columns k T D) : State C S k T D :=
  let next := advance P t s.2.2 (replies P t U)
  (s.1,(A.respond t (s,next),next))

def run (P : Schedule k T) (A : Driver C S k T D B) :
    ℕ → ℕ → State C S k T D → Columns k T D → State C S k T D
  | 0,_,s,_ => s
  | n+1,t,s,U => run P A n (t+1) (step P A t s U) U

theorem replies_measurable (P : Schedule k T) (t : ℕ) :
    Measurable (replies (D:=D) P t) := by
  apply measurable_pi_lambda
  intro i
  by_cases hi : request P t i = true
  · simpa only [replies,if_pos hi] using
      (measurable_pi_apply (column P t i)).comp (measurable_pi_apply i)
  · simpa only [replies,if_neg hi] using
      (measurable_const : Measurable (fun _ : Columns k T D => (0 : Space D)))

theorem step_measurable (P : Schedule k T) (A : Driver C S k T D B) (t : ℕ) :
    Measurable (fun p : State C S k T D × Columns k T D => step P A t p.1 p.2) := by
  have hn : Measurable (fun p : State C S k T D × Columns k T D =>
      advance P t p.1.2.2 (replies P t p.2)) :=
    (advance_measurable P t).comp
      ((measurable_snd.comp (measurable_snd.comp measurable_fst)).prodMk
        ((replies_measurable P t).comp measurable_snd))
  exact (measurable_fst.comp measurable_fst).prodMk
    (((A.respond_measurable t).comp (measurable_fst.prodMk hn)).prodMk hn)

theorem run_measurable (P : Schedule k T) (A : Driver C S k T D B) :
    ∀ n t, Measurable (fun p : State C S k T D × Columns k T D => run P A n t p.1 p.2) := by
  intro n
  induction n with
  | zero => intro t; exact measurable_fst
  | succ n ih =>
    intro t
    exact (ih (t+1)).comp ((step_measurable P A t).prodMk measurable_snd)

theorem run_context (P : Schedule k T) (A : Driver C S k T D B) :
    ∀ n t (s : State C S k T D) U, (run P A n t s U).1 = s.1 := by
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih => intros; exact ih _ _ _

theorem run_actualStore (P : Schedule k T) (A : Driver C S k T D B) :
    ∀ n t (s : State C S k T D) U, s.2.2 = actualStore P t U →
      (run P A n t s U).2.2 = actualStore P (t+n) U := by
  intro n
  induction n with
  | zero => intro t s U h; simpa only [run,Nat.add_zero] using h
  | succ n ih =>
    intro t s U h
    have hn : (step P A t s U).2.2 = actualStore P (t+1) U := by
      change advance P t s.2.2 (replies P t U) = _
      rw [h,advance_actualStore]
    have hh := ih (t+1) (step P A t s U) U hn
    have he : (t+1)+n=t+(n+1) := by omega
    simpa only [run,he] using hh

theorem run_initialStore (P : Schedule k T) (A : Driver C S k T D B)
    (n : ℕ) (c : C) (s : S) (U : Columns k T D) :
    (run P A n 0 (c,(s,initialStore k T D)) U).2.2 = actualStore P n U := by
  simpa only [Nat.zero_add] using
    run_actualStore P A n 0 (c,(s,initialStore k T D)) U (actualStore_zero P U).symm

end Bilevel.TransportAuxiliaryFrame
