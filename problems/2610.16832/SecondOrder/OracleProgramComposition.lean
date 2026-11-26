import SecondOrder.OracleBatchProgram

open MeasureTheory

namespace SecondOrder
namespace OracleProgram

variable {Ξ Q Y O O' : Type}

def prependAnswer (y : Y) (ys : ℕ → Y) : ℕ → Y
  | 0 => y
  | n+1 => ys n

theorem readAnswers_succ_first (p : OracleProgram Q Y O) (ys : ℕ → Y) (n : ℕ) :
    readAnswers p ys (n+1)=readAnswers (advance p (ys 0)) (fun i => ys (i+1)) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [readAnswers,ih,readAnswers]

def view (q₀ : Q) (o₀ : O) (p : OracleProgram Q Y O) : Q × O × Bool :=
  (OracleProgram.query q₀ p,OracleProgram.output o₀ p,finished p)

theorem view_read_bind_zero (q₀ : Q) (o₀ : O) (o₀' : O')
    (p : OracleProgram Q Y O) (f : O → OracleProgram Q Y O') (ys : ℕ → Y) :
    OracleProgram.view q₀ o₀' (readAnswers (bind p f) ys 0)=
      if finished p=true then OracleProgram.view q₀ o₀' (readAnswers (f (OracleProgram.output o₀ p)) ys 0)
      else (OracleProgram.query q₀ p,o₀',false) := by
  cases p <;> rfl

theorem view_read_bind_succ (q₀ : Q) (o₀ : O) (o₀' : O')
    (p : OracleProgram Q Y O) (f : O → OracleProgram Q Y O') (ys : ℕ → Y) (n : ℕ) :
    OracleProgram.view q₀ o₀' (readAnswers (bind p f) ys (n+1))=
      if finished p=true then OracleProgram.view q₀ o₀' (readAnswers (f (OracleProgram.output o₀ p)) ys (n+1))
      else OracleProgram.view q₀ o₀' (readAnswers (bind (advance p (ys 0)) f) (fun i => ys (i+1)) n) := by
  cases p with
  | done o => rfl
  | request q k => exact readAnswers_request q (fun y => bind (k y) f) ys n |> congrArg (OracleProgram.view q₀ o₀')

variable [MeasurableSpace Ξ] [MeasurableSpace Q] [MeasurableSpace Y]
  [MeasurableSpace O] [MeasurableSpace O']

theorem MeasurableFamily.view {q₀ : Q} {o₀ : O} {p : Ξ → OracleProgram Q Y O}
    (hp : MeasurableFamily q₀ o₀ p) (n : ℕ) :
    Measurable (fun w : Ξ × (ℕ → Y) => OracleProgram.view q₀ o₀ (readAnswers (p w.1) w.2 n)) :=
  (hp.query n).prodMk ((hp.output n).prodMk (hp.finished n))

theorem measurableFamily_of_view (q₀ : Q) (o₀ : O) (p : Ξ → OracleProgram Q Y O)
    (h : ∀ n, Measurable (fun w : Ξ × (ℕ → Y) => OracleProgram.view q₀ o₀ (readAnswers (p w.1) w.2 n))) :
    MeasurableFamily q₀ o₀ p :=
  ⟨fun n => (h n).fst,fun n => (h n).snd.fst,fun n => (h n).snd.snd⟩

theorem MeasurableFamily.advance {q₀ : Q} {o₀ : O} {p : Ξ → OracleProgram Q Y O}
    (hp : MeasurableFamily q₀ o₀ p) :
    MeasurableFamily q₀ o₀ (fun w : Ξ × Y => advance (p w.1) w.2) := by
  have hm : Measurable (fun w : (Ξ × Y) × (ℕ → Y) => (w.1.1,prependAnswer w.1.2 w.2)) := by
    apply measurable_fst.fst.prodMk
    apply measurable_pi_lambda
    intro i
    cases i with
    | zero => exact measurable_fst.snd
    | succ n => exact (measurable_pi_apply n).comp measurable_snd
  apply measurableFamily_of_view
  intro n
  simpa only [readAnswers_succ_first,prependAnswer] using (hp.view (n+1)).comp hm

/-- Sequential composition preserves observable-prefix measurability even
when the first subprogram's call count depends on its replies. -/
theorem MeasurableFamily.bind {q₀ : Q} {o₀ : O} {o₀' : O'}
    {p : Ξ → OracleProgram Q Y O} {f : Ξ → O → OracleProgram Q Y O'}
    (hp : MeasurableFamily q₀ o₀ p)
    (hf : MeasurableFamily q₀ o₀' (fun w : Ξ × O => f w.1 w.2)) :
    MeasurableFamily q₀ o₀' (fun ξ => OracleProgram.bind (p ξ) (f ξ)) := by
  classical
  apply measurableFamily_of_view
  intro n
  induction n generalizing Ξ with
  | zero =>
    have he : MeasurableSet {w : Ξ × (ℕ → Y) | OracleProgram.finished (p w.1)=true} :=
      (hp.finished 0) (measurableSet_singleton true)
    have hd : Measurable (fun w : Ξ × (ℕ → Y) =>
        OracleProgram.view q₀ o₀' (readAnswers (f w.1 (OracleProgram.output o₀ (p w.1))) w.2 0)) :=
      (hf.view 0).comp ((measurable_fst.prodMk (hp.output 0)).prodMk measurable_snd)
    have hq : Measurable (fun w : Ξ × (ℕ → Y) => (OracleProgram.query q₀ (p w.1),o₀',false)) :=
      (hp.query 0).prodMk (measurable_const.prodMk measurable_const)
    simpa only [view_read_bind_zero q₀ o₀ o₀'] using Measurable.ite he hd hq
  | succ n ih =>
    have he : MeasurableSet {w : Ξ × (ℕ → Y) | OracleProgram.finished (p w.1)=true} :=
      (hp.finished 0) (measurableSet_singleton true)
    have hd : Measurable (fun w : Ξ × (ℕ → Y) =>
        OracleProgram.view q₀ o₀' (readAnswers (f w.1 (OracleProgram.output o₀ (p w.1))) w.2 (n+1))) :=
      (hf.view (n+1)).comp ((measurable_fst.prodMk (hp.output 0)).prodMk measurable_snd)
    have hf' : MeasurableFamily q₀ o₀' (fun w : (Ξ × Y) × O => f w.1.1 w.2) :=
      hf.comp (fun w : (Ξ × Y) × O => (w.1.1,w.2)) (measurable_fst.fst.prodMk measurable_snd)
    have hn := ih (p := fun w : Ξ × Y => OracleProgram.advance (p w.1) w.2)
      (f := fun w : Ξ × Y => f w.1) hp.advance hf'
    have ht : Measurable (fun w : Ξ × (ℕ → Y) => ((w.1,w.2 0),fun i => w.2 (i+1))) :=
      (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd)).prodMk
        (measurable_pi_lambda _ (fun i => (measurable_pi_apply (i+1)).comp measurable_snd))
    have hr := hn.comp ht
    simp_rw [view_read_bind_succ q₀ o₀ o₀']
    exact Measurable.ite he hd hr

theorem MeasurableFamily.ite {q₀ : Q} {o₀ : O} {p r : Ξ → OracleProgram Q Y O}
    (hp : MeasurableFamily q₀ o₀ p) (hr : MeasurableFamily q₀ o₀ r)
    (s : Set Ξ) [DecidablePred (fun ξ => ξ∈s)] (hs : MeasurableSet s) :
    MeasurableFamily q₀ o₀ (fun ξ => if ξ∈s then p ξ else r ξ) := by
  apply measurableFamily_of_view
  intro n
  have he : (fun w : Ξ × (ℕ → Y) =>
      OracleProgram.view q₀ o₀ (readAnswers (if w.1∈s then p w.1 else r w.1) w.2 n))=
      (fun w : Ξ × (ℕ → Y) => if w.1∈s then OracleProgram.view q₀ o₀ (readAnswers (p w.1) w.2 n)
        else OracleProgram.view q₀ o₀ (readAnswers (r w.1) w.2 n)) := by
    funext w
    split_ifs <;> rfl
  rw [he]
  exact Measurable.ite (hs.preimage measurable_fst) (hp.view n) (hr.view n)

/-- A seed can choose between two measurable program families. -/
theorem MeasurableFamily.prodSum {A B : Type} [MeasurableSpace A] [MeasurableSpace B]
    {q₀ : Q} {o₀ : O} {p : Ξ × A → OracleProgram Q Y O} {r : Ξ × B → OracleProgram Q Y O}
    (hp : MeasurableFamily q₀ o₀ p) (hr : MeasurableFamily q₀ o₀ r) :
    MeasurableFamily q₀ o₀ (fun w : Ξ × (A ⊕ B) =>
      w.2.elim (fun a => p (w.1,a)) (fun b => r (w.1,b))) := by
  apply measurableFamily_of_view
  intro n
  have hpa : Measurable (fun w : (Ξ × (ℕ → Y)) × A => ((w.1.1,w.2),w.1.2)) :=
    (measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd
  have hpb : Measurable (fun w : (Ξ × (ℕ → Y)) × B => ((w.1.1,w.2),w.1.2)) :=
    (measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd
  let fa := fun w : (Ξ × (ℕ → Y)) × A =>
    OracleProgram.view q₀ o₀ (readAnswers (p (w.1.1,w.2)) w.1.2 n)
  let fb := fun w : (Ξ × (ℕ → Y)) × B =>
    OracleProgram.view q₀ o₀ (readAnswers (r (w.1.1,w.2)) w.1.2 n)
  have hs : Measurable (fun w : ((Ξ × (ℕ → Y)) × A) ⊕ ((Ξ × (ℕ → Y)) × B) =>
      w.elim fa fb) := measurable_sum ((hp.view n).comp hpa) ((hr.view n).comp hpb)
  have hm := hs.comp (MeasurableEquiv.prodSumDistrib (Ξ × (ℕ → Y)) A B).measurable
  have ht : Measurable (fun w : (Ξ × (A ⊕ B)) × (ℕ → Y) => ((w.1.1,w.2),w.1.2)) :=
    (measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd
  convert hm.comp ht using 1
  funext w
  rcases w with ⟨⟨ξ,s⟩,ys⟩
  cases s <;> rfl

end OracleProgram
end SecondOrder
