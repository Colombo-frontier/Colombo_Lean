import Bilevel.PolishedSourceFrameBudget
import Bilevel.PolishedSourceMacroProjection
import Bilevel.BorelAdaptiveExecution

/-! A causal selected-frame observer for a flat success counter. The memory
contains an independent context (including the complete OTHER frame), a draw
stream, the public algorithm state, the counter, and only the disclosed
prefix of the SELECTED frame. The evaluator is a Borel function of this
memory and the at-most-one newly disclosed selected column. -/
noncomputable section
open MeasureTheory
namespace Bilevel.PolishedLiteralActualObserver
open EuclideanGaussian ProjectionPosterior TransportControllerMachine SourceFrameActions
set_option autoImplicit false

structure PrefixSchedule (K : ℕ) where
  count : ℕ → ℕ
  zero : count 0=0
  bound : ∀ a,count a≤K
  monotone : Monotone count
  one_step : ∀ a,count (a+1)≤count a+1

variable {K d : ℕ}

def prefixColumns (U : Frame d K) (r : ℕ) : Frame d K := fun i => if i.val<r then U i else 0

theorem prefixColumns_measurable :
    Measurable (fun p : Frame d K × ℕ => prefixColumns p.1 p.2) := by
  apply measurable_from_prod_countable
  intro r
  apply measurable_pi_lambda
  intro i
  by_cases hi : i.val<r
  · simpa only [prefixColumns,if_pos hi] using (measurable_pi_apply i : Measurable (fun U : Frame d K => U i))
  · simpa only [prefixColumns,if_neg hi] using (measurable_const : Measurable (fun _ : Frame d K => (0:Space d)))

variable (P : PrefixSchedule K) (hK : 0<K)

def PrefixSchedule.nextIndex (a : ℕ) : Fin K :=
  if h : P.count a<K then ⟨P.count a,h⟩ else ⟨0,hK⟩

def PrefixSchedule.updateColumns (a : ℕ) (b : Bool) (U : Frame d K) (v : Space d) : Frame d K :=
  if b=true ∧ P.count a<P.count (a+1) then Function.update U (P.nextIndex hK a) v else U

theorem PrefixSchedule.updateColumns_measurable :
    Measurable (fun p : (Frame d K × Space d) × (ℕ × Bool) =>
      P.updateColumns hK p.2.1 p.2.2 p.1.1 p.1.2) := by
  apply measurable_from_prod_countable
  rintro ⟨a,b⟩
  by_cases h : b=true ∧ P.count a<P.count (a+1)
  · simpa only [PrefixSchedule.updateColumns,if_pos h] using
      (measurable_update' (a:=P.nextIndex hK a) :
        Measurable (fun p : Frame d K × Space d => Function.update p.1 (P.nextIndex hK a) p.2))
  · simpa only [PrefixSchedule.updateColumns,if_neg h] using
      (measurable_fst : Measurable (fun p : Frame d K × Space d => p.1))

/-- One live success reveals at most one new selected-frame column. -/
theorem PrefixSchedule.update_actual (a : ℕ) (b : Bool) (U : Frame d K) :
    P.updateColumns hK a b (prefixColumns U (P.count a))
      (if P.count a<P.count (a+1) ∧ b=true then U (P.nextIndex hK a) else 0)=
      prefixColumns U (P.count (a+if b=true then 1 else 0)) := by
  cases hb : b with
  | false => simp only [PrefixSchedule.updateColumns,hb,Bool.false_eq_true,false_and,if_false,Nat.add_zero]
  | true =>
      by_cases hg : P.count a<P.count (a+1)
      · have hi : P.count a<K := lt_of_lt_of_le hg (P.bound (a+1))
        have hs : P.count (a+1)=P.count a+1 := by have := P.one_step a;omega
        simp only [PrefixSchedule.updateColumns,hb,true_and,and_true,if_pos hg,
          if_true,PrefixSchedule.nextIndex,dif_pos hi]
        funext j
        by_cases hj : j=⟨P.count a,hi⟩
        · subst j
          simp [Function.update_self,prefixColumns,hs]
        · have hv : j.val≠P.count a := by intro he;apply hj;exact Fin.ext he
          have he : j.val<P.count (a+1) ↔ j.val<P.count a := by omega
          simp only [Function.update_of_ne hj,prefixColumns,he]
      · have he : P.count (a+1)=P.count a := le_antisymm (not_lt.mp hg) (P.monotone (by omega))
        simp [PrefixSchedule.updateColumns,hb,hg,he]

abbrev ObserverMemory (C S : Type) [MeasurableSpace C] [MeasurableSpace S] (d K : ℕ) :=
  Memory.of (C × ((ℕ → Bool) × (S × (ℕ × Frame d K))))

section Machine
variable {C S Q O Y : Type} [MeasurableSpace C] [MeasurableSpace S] [MeasurableSpace Q]
  [MeasurableSpace O] [MeasurableSpace Y]
  (A : BorelAdaptive.Program S Q O Y)
  (evaluate : C → Q → ℕ → Bool → Frame d K → O)
  (heval : Measurable (fun z : C × (Q × (ℕ × (Bool × Frame d K))) =>
    evaluate z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2))

abbrev H := ObserverMemory C S d K

def request (t : ℕ) (h : H (C:=C) (S:=S) (d:=d) (K:=K)) : Bool :=
  decide (A.halt h.2.2.1=false ∧ h.2.1 t=true ∧ P.count h.2.2.2.1<P.count (h.2.2.2.1+1))

theorem request_measurable (t : ℕ) : Measurable (request (C:=C) (d:=d) P A t) := by
  have hm : Measurable (fun z : Bool × (Bool × ℕ) =>
      decide (z.1=false ∧ z.2.1=true ∧ P.count z.2.2<P.count (z.2.2+1))) := measurable_of_countable _
  have ht : Measurable (fun h : H (C:=C) (S:=S) (d:=d) (K:=K) =>
      (A.halt h.2.2.1,(h.2.1 t,h.2.2.2.1))) :=
    (A.halt_measurable.comp (measurable_fst.comp (measurable_snd.comp measurable_snd))).prodMk
      (((measurable_pi_apply t).comp (measurable_fst.comp measurable_snd)).prodMk
        (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))))
  exact hm.comp ht

def finish (t : ℕ) (z : H (C:=C) (S:=S) (d:=d) (K:=K) × Space d) : H (C:=C) (S:=S) (d:=d) (K:=K) :=
  if A.halt z.1.2.2.1=true then z.1 else
    let b := z.1.2.1 t
    let a := z.1.2.2.2.1
    let columns := P.updateColumns hK a b z.1.2.2.2.2 z.2
    let answer := evaluate z.1.1 (A.query z.1.2.2.1) a b columns
    (z.1.1,(z.1.2.1,(A.update (z.1.2.2.1,answer),(a+if b=true then 1 else 0,columns))))

include heval in
theorem finish_measurable (t : ℕ) : Measurable (finish P hK A evaluate t) := by
  let T := H (C:=C) (S:=S) (d:=d) (K:=K) × Space d
  have hctx : Measurable (fun z : T => z.1.1) := measurable_fst.comp measurable_fst
  have hdraw : Measurable (fun z : T => z.1.2.1) := measurable_fst.comp (measurable_snd.comp measurable_fst)
  have hs : Measurable (fun z : T => z.1.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_fst))
  have ha : Measurable (fun z : T => z.1.2.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_fst)))
  have harr : Measurable (fun z : T => z.1.2.2.2.2) :=
    measurable_snd.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_fst)))
  have hb : Measurable (fun z : T => z.1.2.1 t) := (measurable_pi_apply t).comp hdraw
  have hcolumns : Measurable (fun z : T => P.updateColumns hK z.1.2.2.2.1 (z.1.2.1 t) z.1.2.2.2.2 z.2) :=
    (P.updateColumns_measurable hK).comp ((harr.prodMk measurable_snd).prodMk (ha.prodMk hb))
  have hans : Measurable (fun z : T => evaluate z.1.1 (A.query z.1.2.2.1)
      z.1.2.2.2.1 (z.1.2.1 t) (P.updateColumns hK z.1.2.2.2.1 (z.1.2.1 t) z.1.2.2.2.2 z.2)) :=
    heval.comp (hctx.prodMk ((A.query_measurable.comp hs).prodMk (ha.prodMk (hb.prodMk hcolumns))))
  have hnewa : Measurable (fun z : T => z.1.2.2.2.1+if z.1.2.1 t=true then 1 else 0) :=
    ha.add ((measurable_of_countable (fun b : Bool => if b=true then (1:ℕ) else 0)).comp hb)
  exact measurable_fst.ite ((A.halt_measurable.comp hs) (measurableSet_singleton true))
    (hctx.prodMk (hdraw.prodMk ((A.update_measurable.comp (hs.prodMk hans)).prodMk (hnewa.prodMk hcolumns))))

def rules (first second : Q → Space d) (hfirst : Measurable first) (hsecond : Measurable second)
    (output : Y → Space d) (houtput : Measurable output) : Rules (H (C:=C) (S:=S) (d:=d) (K:=K)) d K where
  first _ h := first (A.query h.2.2.1)
  first_measurable _ := hfirst.comp (A.query_measurable.comp
    (measurable_fst.comp (measurable_snd.comp measurable_snd)))
  second _ h := second (A.query h.2.2.1)
  second_measurable _ := hsecond.comp (A.query_measurable.comp
    (measurable_fst.comp (measurable_snd.comp measurable_snd)))
  request := request P A
  request_measurable := request_measurable P A
  column _ h := P.nextIndex hK h.2.2.2.1
  column_measurable _ := (measurable_of_countable (P.nextIndex hK)).comp
    (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
  finish := finish P hK A evaluate
  finish_measurable := finish_measurable P hK A evaluate heval
  output h := output (A.output h.2.2.1)
  output_measurable := houtput.comp (A.output_measurable.comp
    (measurable_fst.comp (measurable_snd.comp measurable_snd)))

end Machine
end Bilevel.PolishedLiteralActualObserver
