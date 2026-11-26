import SecondOrder.SeededOracleCollection
import Mathlib.Probability.ProductMeasure
import Mathlib.Data.List.NodupEquivFin

open MeasureTheory
open scoped Classical

namespace SecondOrder
noncomputable section

variable {I S : Type} [MeasurableSpace S]

/-- A duplicate-free finite list selects independent coordinates from the
infinite private tape, in the exact list order used by the program. -/
theorem infinitePi_list_measurePreserving (η : Measure S) [IsProbabilityMeasure η]
    (is : List I) (hi : is.Nodup) :
    MeasurePreserving (fun seeds : I → S => fun j : Fin is.length => seeds (is.get j))
      (Measure.infinitePi (fun _ : I => η)) (Measure.pi (fun _ : Fin is.length => η)) := by
  let e : Fin is.length ≃ is.toFinset :=
    (hi.getEquiv is).trans (Equiv.subtypeEquivRight (fun _ => List.mem_toFinset.symm))
  have hrestrict : MeasurePreserving is.toFinset.restrict
      (Measure.infinitePi (fun _ : I => η)) (Measure.pi (fun _ : is.toFinset => η)) :=
    ⟨measurable_pi_lambda _ (fun i => measurable_pi_apply i.val),Measure.infinitePi_map_restrict _⟩
  have hh := (pi_reindex_measurePreserving η e.symm).comp hrestrict
  convert hh using 1

namespace OracleProgram

variable {O : Type}

theorem collectSeedReplies_list (o₀ : O) (g : I → S → O) (is : List I) (seeds : I → S) :
    collectSeedReplies o₀ g is (fun j => seeds (is.get j))=
      (fun i => if i∈is then g i (seeds i) else o₀) := by
  induction is with
  | nil => simp only [collectSeedReplies,List.not_mem_nil,if_false]
  | cons i is ih =>
    have ht : (fun j : Fin is.length => seeds ((i::is).get j.succ))=
        (fun j : Fin is.length => seeds (is.get j)) := rfl
    simp only [collectSeedReplies,List.get_cons_zero,ht,ih]
    funext j
    by_cases hj : j=i
    · subst j
      simp
    · simp [Function.update_of_ne hj,hj]

end OracleProgram
end
end SecondOrder
