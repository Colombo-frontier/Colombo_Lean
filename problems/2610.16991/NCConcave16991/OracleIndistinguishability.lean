import NCConcave16991.Problem
import Mathlib.Data.Finset.Card

/-!
# Exact indistinguishability for unrestricted adaptive component queries

The proof uses the actual full-history interpreter, including early stopping.
No restriction is placed on query locations or on the final output point.
-/

open Set

namespace NCConcave16991.OraclePolicy

noncomputable section

variable {n dx dy : ℕ} {D : ℝ} (K : KnownDualDomain dy D)

def componentSupport (h : History K (n := n) (dx := dx)) : Finset (Fin n) :=
  Finset.univ.image (fun j ↦ (h.2 j).1.1)

theorem mem_componentSupport (h : History K (n := n) (dx := dx)) (i : Fin n) :
    i ∈ componentSupport K h ↔ ∃ j, (h.2 j).1.1 = i := by
  simp [componentSupport]

theorem componentSupport_card (h : History K (n := n) (dx := dx)) :
    (componentSupport K h).card ≤ h.1 := by
  exact (Finset.card_image_le).trans_eq (by simp)

theorem componentSupport_append (h : History K (n := n) (dx := dx))
    (o : Observation K (n := n) (dx := dx)) :
    componentSupport K (appendHistory K h o) = insert o.1.1 (componentSupport K h) := by
  ext i
  rw [Finset.mem_insert, mem_componentSupport, mem_componentSupport]
  constructor
  · rintro ⟨j, hj⟩
    by_cases hlt : j.val < h.1
    · have heq : j = (⟨j.val, hlt⟩ : Fin h.1).castSucc := by ext; rfl
      rw [heq] at hj
      right
      exact ⟨⟨j.val, hlt⟩, by simpa only [appendHistory, Fin.snoc_castSucc] using hj⟩
    · have heq : j = Fin.last h.1 := by
        apply Fin.ext
        change j.val = h.1
        have hjlt : j.val < h.1 + 1 := j.isLt
        omega
      rw [heq] at hj
      left
      simpa only [appendHistory, Fin.snoc_last] using hj.symm
  · rintro (hi | ⟨j, hj⟩)
    · exact ⟨Fin.last h.1, by simpa only [appendHistory, Fin.snoc_last] using hi.symm⟩
    · exact ⟨j.castSucc, by simpa only [appendHistory, Fin.snoc_castSucc] using hj⟩

theorem componentSupport_subset_append (h : History K (n := n) (dx := dx))
    (o : Observation K (n := n) (dx := dx)) :
    componentSupport K h ⊆ componentSupport K (appendHistory K h o) := by
  rw [componentSupport_append]
  exact Finset.subset_insert _ _

theorem runAux_componentSupport_mono {Ω : Type*} [MeasurableSpace Ω]
    (P : AdaptivePolicy K (n := n) (dx := dx) Ω)
    (oracle : OracleQuery n dx K → OracleAnswer dx dy) (seed : Ω) (t : ℕ)
    (h : History K (n := n) (dx := dx)) :
    componentSupport K h ⊆ componentSupport K (runAux K P oracle seed t h).2 := by
  induction t generalizing h with
  | zero => exact Finset.Subset.refl _
  | succ t ih =>
    cases hn : P.next seed h with
    | inl x => simpa only [runAux, hn] using Finset.Subset.refl (componentSupport K h)
    | inr q =>
      simpa only [runAux, hn] using (componentSupport_subset_append K h (q, oracle q)).trans
        (ih (appendHistory K h (q, oracle q)))

/-- If the base run never asks component j, arbitrary changes to that component
produce exactly the same output and full transcript. -/
theorem runAux_eq_of_hidden_component {Ω : Type*} [MeasurableSpace Ω]
    (P : AdaptivePolicy K (n := n) (dx := dx) Ω)
    (base other : OracleQuery n dx K → OracleAnswer dx dy) (seed : Ω)
    (j : Fin n) (hagrees : ∀ q, q.1 ≠ j → other q = base q)
    (t : ℕ) (h : History K (n := n) (dx := dx))
    (hhidden : j ∉ componentSupport K (runAux K P base seed t h).2) :
    runAux K P other seed t h = runAux K P base seed t h := by
  induction t generalizing h with
  | zero => rfl
  | succ t ih =>
    cases hn : P.next seed h with
    | inl x => simp only [runAux, hn]
    | inr q =>
      have hqmem : q.1 ∈ componentSupport K
          (runAux K P base seed t (appendHistory K h (q, base q))).2 := by
        apply runAux_componentSupport_mono K P base seed t (appendHistory K h (q, base q))
        rw [componentSupport_append]
        exact Finset.mem_insert_self _ _
      have hqne : q.1 ≠ j := by
        intro heq
        have hh := hhidden
        simp only [runAux, hn] at hh
        exact hh (heq ▸ hqmem)
      have ho := hagrees q hqne
      simp only [runAux, hn, ho]
      apply ih
      simpa only [runAux, hn] using hhidden

theorem run_eq_of_hidden_component {Ω : Type*} [MeasurableSpace Ω]
    (P : AdaptivePolicy K (n := n) (dx := dx) Ω)
    (base other : OracleQuery n dx K → OracleAnswer dx dy) (seed : Ω)
    (j : Fin n) (hagrees : ∀ q, q.1 ≠ j → other q = base q)
    (budget : ℕ) (hhidden : j ∉ componentSupport K (run K P base seed budget).2) :
    run K P other seed budget = run K P base seed budget :=
  runAux_eq_of_hidden_component K P base other seed j hagrees budget (emptyHistory K) hhidden

theorem run_componentSupport_card {Ω : Type*} [MeasurableSpace Ω]
    (P : AdaptivePolicy K (n := n) (dx := dx) Ω)
    (oracle : OracleQuery n dx K → OracleAnswer dx dy) (seed : Ω) (budget : ℕ) :
    (componentSupport K (run K P oracle seed budget).2).card ≤ budget :=
  (componentSupport_card K _).trans (run_budget K P oracle seed budget)

end

end NCConcave16991.OraclePolicy
