import SecondOrder.OracleProgram

open MeasureTheory

namespace SecondOrder
namespace OracleProgram

variable {Ξ Ξ' Q Y O : Type*}

def finished : OracleProgram Q Y O → Bool
  | .done _ => true
  | .request _ _ => false

theorem readAnswers_done (o : O) (ys : ℕ → Y) (n : ℕ) : readAnswers (Q := Q) (.done o) ys n=.done o := by
  induction n with
  | zero => rfl
  | succ n ih => rw [readAnswers,ih]; rfl

theorem readAnswers_request (q : Q) (k : Y → OracleProgram Q Y O) (ys : ℕ → Y) (n : ℕ) :
    readAnswers (.request q k) ys (n+1)=readAnswers (k (ys 0)) (fun i => ys (i+1)) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [readAnswers,ih,readAnswers]

variable [MeasurableSpace Ξ] [MeasurableSpace Ξ'] [MeasurableSpace Q]
  [MeasurableSpace Y] [MeasurableSpace O]

/-- Measurability is imposed on observable finite prefixes, without putting
a noncanonical sigma-algebra on the continuation function space. -/
structure MeasurableFamily (q₀ : Q) (o₀ : O) (p : Ξ → OracleProgram Q Y O) : Prop where
  query : ∀ n, Measurable (fun w : Ξ × (ℕ → Y) => query q₀ (readAnswers (p w.1) w.2 n))
  output : ∀ n, Measurable (fun w : Ξ × (ℕ → Y) => output o₀ (readAnswers (p w.1) w.2 n))
  finished : ∀ n, Measurable (fun w : Ξ × (ℕ → Y) => finished (readAnswers (p w.1) w.2 n))

theorem MeasurableFamily.comp {q₀ : Q} {o₀ : O} {p : Ξ → OracleProgram Q Y O}
    (hp : MeasurableFamily q₀ o₀ p) (f : Ξ' → Ξ) (hf : Measurable f) :
    MeasurableFamily q₀ o₀ (fun ξ => p (f ξ)) := by
  have hm : Measurable (fun w : Ξ' × (ℕ → Y) => (f w.1,w.2)) := (hf.comp measurable_fst).prodMk measurable_snd
  exact ⟨fun n => (hp.query n).comp hm,fun n => (hp.output n).comp hm,fun n => (hp.finished n).comp hm⟩

theorem measurableFamily_done (q₀ : Q) (o₀ : O) (f : Ξ → O) (hf : Measurable f) :
    MeasurableFamily (Y := Y) q₀ o₀ (fun ξ => .done (f ξ)) := by
  refine ⟨?_,?_,?_⟩ <;> intro n <;> simp only [readAnswers_done,query,output,finished]
  · exact measurable_const
  · exact hf.comp measurable_fst
  · exact measurable_const

theorem measurableFamily_request (q₀ : Q) (o₀ : O) (q : Ξ → Q)
    (k : Ξ → Y → OracleProgram Q Y O) (hq : Measurable q)
    (hk : MeasurableFamily q₀ o₀ (fun w : Ξ × Y => k w.1 w.2)) :
    MeasurableFamily q₀ o₀ (fun ξ => .request (q ξ) (k ξ)) := by
  have ht : Measurable (fun w : Ξ × (ℕ → Y) => ((w.1,w.2 0),fun i => w.2 (i+1))) :=
    (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd)).prodMk
      (measurable_pi_lambda _ (fun i => (measurable_pi_apply (i+1)).comp measurable_snd))
  refine ⟨?_,?_,?_⟩
  · intro n
    cases n with
    | zero => exact hq.comp measurable_fst
    | succ n => simpa only [readAnswers_request] using (hk.query n).comp ht
  · intro n
    cases n with
    | zero => exact measurable_const
    | succ n => simpa only [readAnswers_request] using (hk.output n).comp ht
  · intro n
    cases n with
    | zero => exact measurable_const
    | succ n => simpa only [readAnswers_request] using (hk.finished n).comp ht

theorem algorithm_measurable {q₀ : Q} {o₀ : O} (y₀ : Y) {p : Ξ → OracleProgram Q Y O}
    (hp : MeasurableFamily q₀ o₀ p) :
    MeasurableOracleAlgorithmFamily (fun ξ => algorithm q₀ y₀ o₀ (p ξ)) := by
  refine ⟨⟨measurable_const,hp.query,?_⟩,hp.output⟩
  intro n
  apply measurable_pi_lambda
  intro i
  by_cases hi : i=n
  · subst i
    simpa only [algorithm,Function.update_self] using
      (measurable_snd.snd : Measurable (fun w : Ξ × ((ℕ → Y) × Y) => w.2.2))
  · simpa only [algorithm,Function.update_of_ne hi] using
      ((measurable_pi_apply i).comp measurable_snd.fst :
        Measurable (fun w : Ξ × ((ℕ → Y) × Y) => w.2.1 i))

/-- A finite local routine with arbitrary measurable state transitions. -/
def iterateQueries {S : Type*} (q : S → Q) (update : S → Y → S) (finish : S → O) :
    ℕ → S → OracleProgram Q Y O
  | 0, s => .done (finish s)
  | n+1, s => .request (q s) (fun y => iterateQueries q update finish n (update s y))

theorem iterateQueries_usesAtMost {S : Type*} (q : S → Q) (update : S → Y → S) (finish : S → O)
    (n : ℕ) (s : S) : UsesAtMost n (iterateQueries q update finish n s) := by
  induction n generalizing s with
  | zero => trivial
  | succ n ih => exact fun y => ih (update s y)

theorem iterateQueries_measurable {S : Type*} [MeasurableSpace S] (q₀ : Q) (o₀ : O)
    (q : S → Q) (update : S → Y → S) (finish : S → O)
    (hq : Measurable q) (hu : Measurable (fun w : S × Y => update w.1 w.2))
    (hf : Measurable finish) (n : ℕ) : MeasurableFamily q₀ o₀ (iterateQueries q update finish n) := by
  induction n with
  | zero => exact measurableFamily_done q₀ o₀ finish hf
  | succ n ih =>
    exact measurableFamily_request q₀ o₀ q _ hq (ih.comp (fun w : S × Y => update w.1 w.2) hu)

end OracleProgram
end SecondOrder
