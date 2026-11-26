import SecondOrder.OracleProgramComposition

open MeasureTheory

namespace SecondOrder
namespace OracleProgram

variable {Ξ Q Y O : Type} [MeasurableSpace Ξ] [MeasurableSpace Q]
  [MeasurableSpace Y] [MeasurableSpace O]

/-- A batch length can be selected from the current measurable state.
The selection precedes all replies belonging to the chosen subprogram. -/
theorem MeasurableFamily.chooseNat {q₀ : Q} {o₀ : O}
    (p : ℕ → Ξ → OracleProgram Q Y O) (hp : ∀ k, MeasurableFamily q₀ o₀ (p k))
    (k : Ξ → ℕ) (hk : Measurable k) :
    MeasurableFamily q₀ o₀ (fun ξ => p (k ξ) ξ) := by
  apply measurableFamily_of_view
  intro n
  have he : Measurable (fun w : (Ξ × (ℕ → Y)) × ℕ =>
      OracleProgram.view q₀ o₀ (readAnswers (p w.2 w.1.1) w.1.2 n)) :=
    measurable_from_prod_countable (fun j => (hp j).view n)
  have hpair : Measurable (fun w : Ξ × (ℕ → Y) => (w,k w.1)) :=
    measurable_id.prodMk (hk.comp measurable_fst)
  exact he.comp hpair

/-- The fixed-batch compiler remains measurable when an earlier state
selects its length, query array, and final reply processing function. -/
theorem variableBatch_measurable (q₀ : Q) (o₀ : O)
    (k : Ξ → ℕ) (hk : Measurable k)
    (qs : (n : ℕ) → Ξ → Fin n → Q) (finish : (n : ℕ) → Ξ → (Fin n → Y) → O)
    (hq : ∀ n i, Measurable (fun ξ => qs n ξ i))
    (hf : ∀ n, Measurable (fun w : Ξ × (Fin n → Y) => finish n w.1 w.2)) :
    MeasurableFamily q₀ o₀ (fun ξ => batch (k ξ) (qs (k ξ) ξ) (finish (k ξ) ξ)) :=
  MeasurableFamily.chooseNat (fun n ξ => batch n (qs n ξ) (finish n ξ))
    (fun n => batch_measurable q₀ o₀ n (qs n) (finish n) (hq n) (hf n)) k hk

end OracleProgram
end SecondOrder
