import SecondOrder.OracleProgramCollection
import SecondOrder.OracleProgramSeededBind
import SecondOrder.OracleProgramMapLaw
import SecondOrder.FiniteSeedExtension

open MeasureTheory ProbabilityTheory
open scoped Classical

namespace SecondOrder
namespace OracleProgram
noncomputable section

variable {I Q Y O S : Type}

/-- The listed programs receive separate seeds, in their query order. -/
def collectSeedList (o₀ : O) (p : I → S → OracleProgram Q Y O) :
    (is : List I) → (Fin is.length → S) → OracleProgram Q Y (I → O)
  | [], _ => .done (fun _ => o₀)
  | i::is, seeds => bind (p i (seeds (0 : Fin (is.length+1)))) (fun o =>
      bind (collectSeedList o₀ p is (fun j => seeds j.succ))
        (fun os => .done (Function.update os i o)))

theorem collectSeedList_usesAtMost (o₀ : O) (p : I → S → OracleProgram Q Y O)
    (cost : I → ℕ) (hp : ∀ i s, UsesAtMost (cost i) (p i s))
    (is : List I) (seeds : Fin is.length → S) :
    UsesAtMost ((is.map cost).sum) (collectSeedList o₀ p is seeds) := by
  induction is with
  | nil => trivial
  | cons i is ih =>
    apply usesAtMost_bind (hp i (seeds (0 : Fin (is.length+1))))
    intro o
    have hh := usesAtMost_bind (ih (fun j => seeds j.succ))
      (fun os => .done (Function.update os i o)) (m := 0) (fun _ => trivial)
    simpa only [Nat.add_zero] using hh

theorem collectSeedList_eq_collectList (o₀ : O) (p : I → S → OracleProgram Q Y O)
    (is : List I) (seeds : I → S) :
    collectSeedList o₀ p is (fun j => seeds (is.get j))=
      collectList o₀ (fun i => p i (seeds i)) is := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    have ht : (fun j : Fin is.length => seeds ((i::is).get j.succ))=
        (fun j : Fin is.length => seeds (is.get j)) := rfl
    simp only [collectSeedList,collectList,List.get_cons_zero,ht,ih]

def collectSeedReplies (o₀ : O) (g : I → S → O) :
    (is : List I) → (Fin is.length → S) → I → O
  | [], _ => fun _ => o₀
  | i::is, seeds => Function.update
      (collectSeedReplies o₀ g is (fun j => seeds j.succ)) i (g i (seeds (0 : Fin (is.length+1))))

theorem collectSeedList_done (o₀ : O) (g : I → S → O)
    (is : List I) (seeds : Fin is.length → S) :
    collectSeedList (Q := Q) (Y := Y) o₀ (fun i s => .done (g i s)) is seeds=
      .done (collectSeedReplies o₀ g is seeds) := by
  induction is with
  | nil => rfl
  | cons i is ih => simp only [collectSeedList,bind_done,ih,collectSeedReplies]

variable [MeasurableSpace Q] [MeasurableSpace Y] [MeasurableSpace O] [MeasurableSpace S]

theorem collectSeedList_measurable (q₀ : Q) (o₀ : O) (p : I → S → OracleProgram Q Y O)
    (hp : ∀ i, MeasurableFamily q₀ o₀ (p i)) (is : List I) :
    MeasurableFamily q₀ (fun _ => o₀) (collectSeedList o₀ p is) := by
  induction is with
  | nil => exact measurableFamily_done q₀ (fun _ => o₀) _ measurable_const
  | cons i is ih =>
    apply ((hp i).comp (fun seeds : Fin (is.length+1) → S => seeds 0) (measurable_pi_apply 0)).bind
    have ht := ih.comp (fun w : (Fin (i::is).length → S) × O => fun j => w.1 j.succ)
      (measurable_pi_lambda _ (fun j => (measurable_pi_apply j.succ).comp measurable_fst))
    apply ht.bind
    apply measurableFamily_done
    exact (measurable_update_reply i).comp (measurable_fst.snd.prodMk measurable_snd)

theorem collectSeedReplies_measurable (o₀ : O) (g : I → S → O)
    (hg : ∀ i, Measurable (g i)) (is : List I) : Measurable (collectSeedReplies o₀ g is) := by
  induction is with
  | nil => exact measurable_const
  | cons i is ih =>
    exact (measurable_update_reply i).comp
      (((hg i).comp (measurable_pi_apply (0 : Fin (is.length+1)))).prodMk
        (ih.comp (measurable_pi_lambda _ (fun j => measurable_pi_apply j.succ))))

end
end OracleProgram
end SecondOrder
