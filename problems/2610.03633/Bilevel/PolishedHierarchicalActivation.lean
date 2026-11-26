import Bilevel.BorelAdaptiveActivation
import Bilevel.BorelAdaptiveCoupling
import Bilevel.MultiscaleRisk

/-! The literal two-level activation protocol. Only the original algorithm
state receives the full virtual reply. The auxiliary counter increases by
one on each successful live original call. Its capped value determines the
macro/micro prefix; no geometric progress of the query is assumed. -/
noncomputable section
open MeasureTheory
namespace Bilevel.PolishedHierarchicalActivation
open BorelAdaptive
variable {S Q O Y I Private : Type*} [MeasurableSpace S] [MeasurableSpace Q]
  [MeasurableSpace O] [MeasurableSpace Y] [MeasurableSpace I] [MeasurableSpace Private]

def instrument (A : Program S Q O Y) : Program (S × ℕ) (Q × ℕ) (O × ℕ) Y where
  query s := (A.query s.1,s.2)
  query_measurable := (A.query_measurable.comp measurable_fst).prodMk measurable_snd
  update p := (A.update (p.1.1,p.2.1),p.2.2)
  update_measurable := (A.update_measurable.comp
    ((measurable_fst.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd))).prodMk
      (measurable_snd.comp measurable_snd)
  halt s := A.halt s.1
  halt_measurable := A.halt_measurable.comp measurable_fst
  output s := A.output s.1
  output_measurable := A.output_measurable.comp measurable_fst

def response (T : ℕ) (evaluate : I → Q → ℕ → Bool → O)
    (i : I) (q : Q × ℕ) (b : Bool) : O × ℕ :=
  (evaluate i q.1 (min T q.2) b,q.2+if b then 1 else 0)

def initial (s : Private → S) (p : Private) : S × ℕ := (s p,0)

theorem response_measurable (T : ℕ) (evaluate : I → Q → ℕ → Bool → O)
    (he : Measurable (fun p : I × (Q × (ℕ × Bool)) => evaluate p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Measurable (fun p : I × ((Q × ℕ) × Bool) => response T evaluate p.1 p.2.1 p.2.2) := by
  unfold response
  have hn : Measurable (fun p : I × ((Q × ℕ) × Bool) => min T p.2.1.2) :=
    (measurable_of_countable (fun n => min T n)).comp
      (measurable_snd.comp (measurable_fst.comp measurable_snd))
  refine (he.comp (measurable_fst.prodMk
    ((measurable_fst.comp (measurable_fst.comp measurable_snd)).prodMk
      (hn.prodMk (measurable_snd.comp measurable_snd))))).prodMk ?_
  exact (measurable_snd.comp (measurable_fst.comp measurable_snd)).add
    ((measurable_of_countable (fun b : Bool => if b then (1:ℕ) else 0)).comp
      (measurable_snd.comp measurable_snd))

def run (A : Program S Q O Y) (T : ℕ) (evaluate : I → Q → ℕ → Bool → O)
    (s : Private → S) (n : ℕ) (p : Sample I Private Bool) : S × ℕ :=
  seededState (instrument A) (response T evaluate) (initial s) n p

omit [MeasurableSpace I] [MeasurableSpace Private] in
theorem run_count (A : Program S Q O Y) (T : ℕ) (evaluate : I → Q → ℕ → Bool → O)
    (s : Private → S) (n : ℕ) (p : Sample I Private Bool) :
    (run A T evaluate s n p).2=successes (instrument A) (response T evaluate) (initial s) n p := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (BorelAdaptive.step (instrument A) (response T evaluate) p.1 (p.2.2 n)
      (run A T evaluate s n p)).2 = _
    simp only [successes]
    change _ = successes (instrument A) (response T evaluate) (initial s) n p +
      if A.halt (run A T evaluate s n p).1=false ∧ p.2.2 n=true then 1 else 0
    cases hh : A.halt (run A T evaluate s n p).1 <;> cases hb : p.2.2 n <;>
      simp only [BorelAdaptive.step,instrument,hh,hb,response,
        Bool.false_eq_true,if_false,if_true,Bool.true_eq_false,and_self,and_false,false_and,
        true_and,Nat.add_zero,ih]

omit [MeasurableSpace I] [MeasurableSpace Private] in
theorem actual_virtual_state (A : Program S Q O Y) (T : ℕ)
    (evaluate : I → Q → ℕ → Bool → O) (original : I → Q → Bool → O)
    (s : Private → S) (n : ℕ) (p : Sample I Private Bool)
    (hlocal : ∀ t<n, A.halt (run A T evaluate s t p).1=false →
      original p.1 (A.query (run A T evaluate s t p).1) (p.2.2 t)=
        evaluate p.1 (A.query (run A T evaluate s t p).1)
          (min T (run A T evaluate s t p).2) (p.2.2 t)) :
    seededState A original s n p=(run A T evaluate s n p).1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hp := ih (fun t ht => hlocal t (by omega))
    change BorelAdaptive.step A original p.1 (p.2.2 n) (seededState A original s n p) = _
    rw [hp]
    change BorelAdaptive.step A original p.1 (p.2.2 n) (run A T evaluate s n p).1 =
      (BorelAdaptive.step (instrument A) (response T evaluate) p.1 (p.2.2 n)
        (run A T evaluate s n p)).1
    cases hh : A.halt (run A T evaluate s n p).1
    · have he := hlocal n (by omega) hh
      simp only [BorelAdaptive.step,instrument,hh,Bool.false_eq_true,if_false,response,he]
    · simp only [BorelAdaptive.step,instrument,hh,if_true]

theorem prefix_incomplete {M stages a : ℕ} (hM : 0<M) (ha : a<stages*M) :
    min (stages*M) a=a ∧ (min (stages*M) a)/M<stages := by
  rw [Nat.min_eq_right ha.le]
  exact ⟨rfl,(Nat.div_lt_iff_lt_mul hM).mpr ha⟩

theorem activation_sixteenth (A : Program S Q O Y) (T : ℕ)
    (evaluate : I → Q → ℕ → Bool → O) (s : Private → S)
    (ν : Measure I) [IsProbabilityMeasure ν] (ρ : Measure Private) [IsProbabilityMeasure ρ]
    (p : ℝ) (hp : 0<p) (hp1 : p≤1) (n : ℕ) (hT : 0<T)
    (hn : (n:ℝ)≤(T:ℝ)/(16*p)) :
    (ν.prod (ρ.prod (IndependentStream.law (BernoulliOracle.law p hp1)))).real
      {z | T≤(run A T evaluate s n z).2}≤1/16 := by
  simp only [run_count]
  exact BorelAdaptive.activation_sixteenth (instrument A) (response T evaluate)
    (initial s) ν ρ p hp hp1 n T hT hn

omit [MeasurableSpace I] [MeasurableSpace Private] in
theorem capped_margin_on_good (A : Program S Q O Y) (T : ℕ)
    (evaluate : I → Q → ℕ → Bool → O) (original : I → Q → Bool → O)
    (s : Private → S) (n : ℕ) (z : Sample I Private Bool)
    (loss : I × Y → ℝ) (ε : ℝ)
    (hlocal : ∀ t<n, A.halt (run A T evaluate s t z).1=false →
      original z.1 (A.query (run A T evaluate s t z).1) (z.2.2 t)=
        evaluate z.1 (A.query (run A T evaluate s t z).1)
          (min T (run A T evaluate s t z).2) (z.2.2 t))
    (hact : ¬T≤(run A T evaluate s n z).2)
    (hbarrier : (run A T evaluate s n z).2<T →
      8*ε≤loss (z.1,A.output (run A T evaluate s n z).1)) :
    8*ε≤loss (seededCapped A original s n z) := by
  change 8*ε≤loss (z.1,A.output (seededState A original s n z))
  rw [actual_virtual_state A T evaluate original s n z hlocal]
  exact hbarrier (Nat.lt_of_not_ge hact)

end Bilevel.PolishedHierarchicalActivation
