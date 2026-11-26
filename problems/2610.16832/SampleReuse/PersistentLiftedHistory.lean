import SampleReuse.PersistentHistoryEvents

open SecondOrder
open scoped Classical
namespace SampleReuse
noncomputable section
variable {H S A Key : Type}

theorem tableHistory_liftPublic (query : ∀ n, FiniteHistory S A n → Key)
    (θ : H) (s : S) (table : Key → A) : ∀ n,
    finiteHistoryMapInitial Prod.snd n (tableHistory (liftPublicQuery query) (θ, s) table n) =
      tableHistory query s table n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    change (finiteHistoryMapInitial Prod.snd n (tableHistory (liftPublicQuery query) (θ, s) table n),
      table (query n (finiteHistoryMapInitial Prod.snd n (tableHistory (liftPublicQuery query) (θ, s) table n)))) = _
    rw [ih]
    rfl

theorem lifted_table_charge_le (query : ∀ n, FiniteHistory S A n → Key) (target : Key → Prop)
    (θ : H) (s : S) (table : Key → A) (cap n : ℕ) :
    kernelChargeCount (stageSelected (targetDisclosure query target)) cap n
      (tableHistory (liftPublicQuery query) (θ, s) table n) ≤
      tableResponseCount query target s table n := by
  letI : MeasurableSpace H := ⊤
  letI : MeasurableSpace S := ⊤
  letI : MeasurableSpace A := ⊤
  unfold stageSelected
  rw [kernelChargeCount_hidden, tableHistory_liftPublic]
  exact kernelChargeCount_table_le query target s table cap n

end
end SampleReuse
