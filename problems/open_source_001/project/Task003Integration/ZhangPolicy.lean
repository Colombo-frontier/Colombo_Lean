import Task003Base
import Nonsmooth.HistoryPolicy

noncomputable section
set_option autoImplicit false
namespace Task003Integration
open MeasureTheory Task003.OracleSimulation

abbrev ZhangPoint (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev ZhangBall (d : ℕ) := {x : ZhangPoint d // ‖x‖ ≤ 1}

def zhangZero (d : ℕ) : ZhangBall d := ⟨0, by simp⟩

def zhangFrozen {d : ℕ} (b : SourcePolicy d Unit) :
    (n : ℕ) → (Fin n → ℝ) → Bool × ZhangBall d
  | 0, _ => (false, zhangZero d)
  | n + 1, h =>
    let old := zhangFrozen b n (Fin.init h)
    if old.1 then old else
      if b.stop n ((), Fin.init h) then
        (true, ⟨b.output n ((), Fin.init h), b.output_feasible n _⟩)
      else (false, zhangZero d)

def zhangQuery {d : ℕ} (b : SourcePolicy d Unit) (n : ℕ) (h : Fin n → ℝ) : ZhangBall d :=
  if (zhangFrozen b n h).1 then zhangZero d else
    if b.stop n ((),h) then zhangZero d else ⟨b.query n ((),h),b.query_feasible n _⟩

def zhangOutput {d : ℕ} (b : SourcePolicy d Unit) (n : ℕ) (h : Fin n → ℝ) : ZhangBall d :=
  if (zhangFrozen b n h).1 then (zhangFrozen b n h).2
  else ⟨b.output n ((),h),b.output_feasible n _⟩

theorem zhangFrozen_measurable {d : ℕ} (b : SourcePolicy d Unit) (n : ℕ) :
    Measurable (zhangFrozen b n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hi : Measurable (Fin.init : (Fin (n+1) → ℝ) → (Fin n → ℝ)) :=
      measurable_pi_lambda _ (fun j => measurable_pi_apply j.castSucc)
    have hs := ih.comp hi
    have hp : Measurable (fun h : Fin (n+1) → ℝ => ((),Fin.init h)) :=
      measurable_const.prodMk hi
    exact Measurable.ite (measurableSet_eq_fun hs.fst measurable_const) hs
      (Measurable.ite (measurableSet_eq_fun ((b.stop_measurable n).comp hp) measurable_const)
        (measurable_const.prodMk (((b.output_measurable n).comp hp).subtype_mk)) measurable_const)

theorem zhangQuery_measurable {d : ℕ} (b : SourcePolicy d Unit) (n : ℕ) :
    Measurable (zhangQuery b n) := by
  have hp : Measurable (fun h : Fin n → ℝ => ((),h)) := measurable_const.prodMk measurable_id
  exact Measurable.ite (measurableSet_eq_fun (zhangFrozen_measurable b n).fst measurable_const)
    measurable_const
    (Measurable.ite (measurableSet_eq_fun ((b.stop_measurable n).comp hp) measurable_const)
      measurable_const (((b.query_measurable n).comp hp).subtype_mk))

theorem zhangOutput_measurable {d : ℕ} (b : SourcePolicy d Unit) (n : ℕ) :
    Measurable (zhangOutput b n) := by
  have hp : Measurable (fun h : Fin n → ℝ => ((),h)) := measurable_const.prodMk measurable_id
  exact Measurable.ite (measurableSet_eq_fun (zhangFrozen_measurable b n).fst measurable_const)
    (zhangFrozen_measurable b n).snd (((b.output_measurable n).comp hp).subtype_mk)

def zhangFollow {d : ℕ} (b : SourcePolicy d Unit) (f : ZhangPoint d → ℝ) :
    (fuel n : ℕ) → (Fin n → ℝ) → ZhangBall d
  | 0, n, h => zhangOutput b n h
  | fuel+1, n, h => zhangFollow b f fuel (n+1) (Fin.snoc h (f (zhangQuery b n h).val))

theorem zhangFollow_execute {d : ℕ} (b : SourcePolicy d Unit) (f : ZhangPoint d → ℝ)
    (fuel n : ℕ) (h : Fin n → ℝ) :
    (zhangFollow b f fuel n h).val =
      if (zhangFrozen b n h).1 then (zhangFrozen b n h).2.val
      else b.execute f fuel n ((),h) := by
  induction fuel generalizing n with
  | zero =>
    cases hf : (zhangFrozen b n h).1 <;> simp [zhangFollow,zhangOutput,SourcePolicy.execute,hf]
  | succ fuel ih =>
    rw [zhangFollow,ih]
    cases hf : (zhangFrozen b n h).1 <;> cases hs : b.stop n ((),h) <;>
      simp [zhangFrozen,zhangQuery,SourcePolicy.execute,SourcePolicy.nextHistory,hf,hs]

def zhangReplies {d : ℕ} (b : SourcePolicy d Unit) (f : ZhangPoint d → ℝ) :
    (n : ℕ) → Fin n → ℝ
  | 0 => Fin.elim0
  | n+1 => Fin.snoc (zhangReplies b f n) (f (zhangQuery b n (zhangReplies b f n)).val)

theorem zhangFollow_replies {d : ℕ} (b : SourcePolicy d Unit) (f : ZhangPoint d → ℝ)
    (fuel n : ℕ) :
    zhangFollow b f fuel n (zhangReplies b f n) =
      zhangOutput b (n+fuel) (zhangReplies b f (n+fuel)) := by
  induction fuel generalizing n with
  | zero => rfl
  | succ fuel ih =>
    change zhangFollow b f fuel (n+1) (zhangReplies b f (n+1)) = _
    rw [ih]
    have hn : n+1+fuel = n+(fuel+1) := by omega
    rw [hn]

theorem zhangOutput_replies {d : ℕ} (b : SourcePolicy d Unit) (f : ZhangPoint d → ℝ) (N : ℕ) :
    (zhangOutput b N (zhangReplies b f N)).val = b.run f N () := by
  have hp := zhangFollow_replies b f N 0
  have he := zhangFollow_execute b f N 0 Fin.elim0
  rw [Nat.zero_add] at hp
  exact (congrArg Subtype.val hp).symm.trans he

def zhangHalfHistory {d n : ℕ} (h : Nonsmooth.History (ZhangBall d) n) : Fin n → ℝ :=
  fun i => (h i).2 / 2

theorem zhangHalfHistory_measurable (d n : ℕ) : Measurable (@zhangHalfHistory d n) := by
  exact measurable_pi_lambda _ (fun i => (measurable_pi_apply i).snd.div_const 2)

def zhangHistoryPolicy {d : ℕ} (b : SourcePolicy d Unit) : Nonsmooth.HistoryPolicy Unit (ZhangBall d) where
  query n _ h := zhangQuery b n (zhangHalfHistory h)
  output n _ h := zhangOutput b n (zhangHalfHistory h)

theorem zhangHistoryPolicy_measurable {d : ℕ} (b : SourcePolicy d Unit) :
    (zhangHistoryPolicy b).IsMeasurable := by
  exact ⟨fun n => (zhangQuery_measurable b n).comp
    ((zhangHalfHistory_measurable d n).comp measurable_snd),
    fun n => (zhangOutput_measurable b n).comp
    ((zhangHalfHistory_measurable d n).comp measurable_snd)⟩

theorem zhangHistoryPolicy_replies {d : ℕ} (b : SourcePolicy d Unit) (f : ZhangPoint d → ℝ) (n : ℕ) :
    zhangHalfHistory ((zhangHistoryPolicy b).transcript (fun x => f x.val) () n) =
      zhangReplies b (fun x => f x / 2) n := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [zhangHalfHistory,Nonsmooth.HistoryPolicy.transcript,
        Fin.snoc_last,zhangHistoryPolicy,zhangReplies] using
        congrArg (fun h => f (zhangQuery b n h).val / 2) ih
    · simpa only [zhangHalfHistory,Nonsmooth.HistoryPolicy.transcript,
        zhangReplies,Fin.snoc_castSucc] using congrFun ih j

def zhangStatePolicy {d : ℕ} (b : SourcePolicy d Unit) (N : ℕ) :
    Nonsmooth.Policy Unit (Nonsmooth.HistoryStore (ZhangBall d)) (ZhangBall d) :=
  (zhangHistoryPolicy b).toState N (zhangZero d)

theorem zhangStatePolicy_measurable {d : ℕ} (b : SourcePolicy d Unit) (N : ℕ) :
    (zhangStatePolicy b N).IsMeasurable :=
  Nonsmooth.history_toState_measurable (zhangHistoryPolicy_measurable b) N (zhangZero d)

theorem zhangStatePolicy_result {d : ℕ} (b : SourcePolicy d Unit) (N : ℕ) (f : ZhangPoint d → ℝ) :
    ((zhangStatePolicy b N).result (fun x => f x.val) () N).val =
      b.run (fun x => f x / 2) N () := by
  rw [zhangStatePolicy,Nonsmooth.history_toState_result]
  change (zhangOutput b N (zhangHalfHistory ((zhangHistoryPolicy b).transcript
    (fun x => f x.val) () N))).val = _
  rw [zhangHistoryPolicy_replies,zhangOutput_replies]

end Task003Integration
