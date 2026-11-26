import SecondOrder.ExactOracleProgram

open MeasureTheory

namespace SecondOrder
namespace OracleProgram
noncomputable section
open scoped Classical

variable {I Q Y O Ξ : Type}

/-- Execute precisely the listed subprograms and retain each actual reply.
Unlisted coordinates retain the specified default value. -/
def collectList (o₀ : O) (p : I → OracleProgram Q Y O) :
    List I → OracleProgram Q Y (I → O)
  | [] => .done (fun _ => o₀)
  | i::is => bind (p i) (fun o => bind (collectList o₀ p is)
      (fun os => .done (Function.update os i o)))

theorem collectList_usesExactly (o₀ : O) (p : I → OracleProgram Q Y O)
    (cost : I → ℕ) (hp : ∀ i, UsesExactly (cost i) (p i)) (is : List I) :
    UsesExactly ((is.map cost).sum) (collectList o₀ p is) := by
  induction is with
  | nil => trivial
  | cons i is ih =>
    simp only [collectList,List.map_cons,List.sum_cons]
    apply (hp i).bind
    intro o
    have hh := ih.bind (fun os => .done (Function.update os i o)) (M := 0) (fun _ => trivial)
    simpa only [Nat.add_zero] using hh

variable [MeasurableSpace Ξ] [MeasurableSpace Q] [MeasurableSpace Y] [MeasurableSpace O]

theorem measurable_update_reply (i : I) :
    Measurable (fun w : O × (I → O) => Function.update w.2 i w.1) := by
  apply measurable_pi_lambda
  intro j
  by_cases hj : j=i
  · subst j
    simpa only [Function.update_same] using (measurable_fst : Measurable (fun w : O × (I → O) => w.1))
  · simpa only [Function.update_of_ne hj] using
      ((measurable_pi_apply j).comp (measurable_snd : Measurable (fun w : O × (I → O) => w.2)))

theorem collectList_measurable (q₀ : Q) (o₀ : O) (p : Ξ → I → OracleProgram Q Y O)
    (hp : ∀ i, MeasurableFamily q₀ o₀ (fun ξ => p ξ i)) (is : List I) :
    MeasurableFamily q₀ (fun _ => o₀) (fun ξ => collectList o₀ (p ξ) is) := by
  induction is with
  | nil => exact measurableFamily_done q₀ (fun _ => o₀) _ measurable_const
  | cons i is ih =>
    apply (hp i).bind
    have ht := ih.comp (fun w : Ξ × O => w.1) measurable_fst
    apply ht.bind
    apply measurableFamily_done
    exact (measurable_update_reply i).comp (measurable_fst.snd.prodMk measurable_snd)

end
end OracleProgram
end SecondOrder
