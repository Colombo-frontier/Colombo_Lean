import Bilevel.ChiHierarchyReply
import Bilevel.BorelAdaptiveActivation

/-! Actual halted source-genie execution. The original program sees only
the full virtual SFO reply. A separate finite store receives the requested
new columns on the current successful coin, then evaluates that reply from
the old/new disclosed arrays. -/
noncomputable section
open MeasureTheory
namespace Bilevel.ChiHierarchyExecution
open ChiHierarchyIndex BorelAdaptive

variable {E S Q O Y : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
  [MeasurableSpace S] [MeasurableSpace Q] [MeasurableSpace O] [MeasurableSpace Y]

def instrument (counts : ℕ → ℕ) (J : ℕ) (A : Program S Q O Y) :
    Program (S × Store counts J E) (Q × Store counts J E) (O × Store counts J E) Y where
  query h := (A.query h.1,h.2)
  query_measurable := (A.query_measurable.comp measurable_fst).prodMk measurable_snd
  update p := (A.update (p.1.1,p.2.1),p.2.2)
  update_measurable := (A.update_measurable.comp
    ((measurable_fst.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd))).prodMk
      (measurable_snd.comp measurable_snd)
  halt h := A.halt h.1
  halt_measurable := A.halt_measurable.comp measurable_fst
  output h := A.output h.1
  output_measurable := A.output_measurable.comp measurable_fst

def response (counts : ℕ → ℕ) (J : ℕ)
    (evaluate : Q → Store counts J E → Store counts J E → Bool → O)
    (U : FiniteColumns counts J E) (p : Q × Store counts J E) (b : Bool) : O × Store counts J E :=
  let next := ChiHierarchyIndex.update counts J p.2 b (revealReply counts J p.2.1 b U)
  (evaluate p.1 p.2 next b,next)

theorem response_measurable (counts : ℕ → ℕ) (J : ℕ)
    (evaluate : Q → Store counts J E → Store counts J E → Bool → O)
    (he : Measurable (fun p : Q × (Store counts J E × (Store counts J E × Bool)) =>
      evaluate p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Measurable (fun p : FiniteColumns counts J E × ((Q × Store counts J E) × Bool) =>
      response counts J evaluate p.1 p.2.1 p.2.2) := by
  let T := FiniteColumns counts J E × ((Q × Store counts J E) × Bool)
  have ho : Measurable (fun p : T => p.2.1.2) := measurable_snd.comp (measurable_fst.comp measurable_snd)
  have hb : Measurable (fun p : T => p.2.2) := measurable_snd.comp measurable_snd
  have hq : Measurable (fun p : T => p.2.1.1) := measurable_fst.comp (measurable_fst.comp measurable_snd)
  have hr : Measurable (fun p : T => revealReply counts J p.2.1.2.1 p.2.2 p.1) :=
    (revealReply_joint_measurable counts J).comp (measurable_fst.prodMk ((measurable_fst.comp ho).prodMk hb))
  have hn : Measurable (fun p : T => ChiHierarchyIndex.update counts J p.2.1.2 p.2.2
      (revealReply counts J p.2.1.2.1 p.2.2 p.1)) :=
    (ChiHierarchyIndex.update_measurable counts J).comp (ho.prodMk (hb.prodMk hr))
  exact (he.comp (hq.prodMk (ho.prodMk (hn.prodMk hb)))).prodMk hn

def initialState (counts : ℕ → ℕ) (J : ℕ) (s : S) : S × Store counts J E :=
  (s,ChiHierarchyIndex.initial counts J)

theorem initialize_measurable (counts : ℕ → ℕ) (J : ℕ) :
    Measurable (initialState (E:=E) (S:=S) counts J) := measurable_id.prodMk measurable_const

def run (counts : ℕ → ℕ) (J : ℕ) (A : Program S Q O Y)
    (evaluate : Q → Store counts J E → Store counts J E → Bool → O)
    (U : FiniteColumns counts J E) (s : S) (draws : ℕ → Bool) (n : ℕ) : S × Store counts J E :=
  BorelAdaptive.run (instrument counts J A) (response counts J evaluate) U draws (initialState counts J s) n

theorem run_store (counts : ℕ → ℕ) (J : ℕ) (A : Program S Q O Y)
    (evaluate : Q → Store counts J E → Store counts J E → Bool → O)
    (U : FiniteColumns counts J E) (s : S) (draws : ℕ → Bool) (n : ℕ) :
    (run counts J A evaluate U s draws n).2 =
      actual counts J (run counts J A evaluate U s draws n).2.1 U := by
  induction n with
  | zero => exact (actual_zero counts J U).symm
  | succ n ih =>
    change (BorelAdaptive.step (instrument counts J A) (response counts J evaluate) U (draws n)
      (run counts J A evaluate U s draws n)).2 =
      actual counts J (BorelAdaptive.step (instrument counts J A) (response counts J evaluate) U (draws n)
        (run counts J A evaluate U s draws n)).2.1 U
    unfold BorelAdaptive.step
    split_ifs with hh
    · exact ih
    · change ChiHierarchyIndex.update counts J (run counts J A evaluate U s draws n).2 (draws n)
          (revealReply counts J (run counts J A evaluate U s draws n).2.1 (draws n) U) =
        actual counts J (ChiHierarchyIndex.update counts J (run counts J A evaluate U s draws n).2 (draws n)
          (revealReply counts J (run counts J A evaluate U s draws n).2.1 (draws n) U)).1 U
      rw [ih]
      have hq : (actual counts J (run counts J A evaluate U s draws n).2.1 U).1 =
          (run counts J A evaluate U s draws n).2.1 := rfl
      rw [hq,update_actual counts J (run counts J A evaluate U s draws n).2.1 (draws n) U]
      rfl

theorem run_success_count (counts : ℕ → ℕ) (J : ℕ) (A : Program S Q O Y)
    (evaluate : Q → Store counts J E → Store counts J E → Bool → O)
    (U : FiniteColumns counts J E) (s : S) (draws : ℕ → Bool) (n : ℕ) :
    (run counts J A evaluate U s draws n).2.1 =
      successes (instrument counts J A) (response counts J evaluate) (initialState counts J) n (U,(s,draws)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (BorelAdaptive.step (instrument counts J A) (response counts J evaluate) U (draws n)
      (run counts J A evaluate U s draws n)).2.1 = _
    simp only [successes,seededState]
    change _ = successes (instrument counts J A) (response counts J evaluate) (initialState counts J) n (U,(s,draws)) +
      if A.halt (run counts J A evaluate U s draws n).1=false ∧ draws n=true then 1 else 0
    cases hh : A.halt (run counts J A evaluate U s draws n).1 <;>
      cases hb : draws n <;>
      simp only [BorelAdaptive.step,instrument,hh,hb,response,ChiHierarchyIndex.update,
        Bool.false_eq_true,if_false,if_true,Bool.true_eq_false,and_self,and_false,false_and,
        true_and,Nat.add_zero,ih]

end Bilevel.ChiHierarchyExecution
