import Mathlib.Tactic

namespace RandomizedFO2003

open scoped BigOperators

/-- Merge repeated finite nodes without changing the integral of any function.
Strict positivity is preserved and the support cardinality cannot increase. -/
theorem merge_positive_weights {X : Type} {n : ℕ}
    (node : Fin n → X) (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) :
    ∃ k : ℕ, k ≤ n ∧ ∃ (point : Fin k → X) (weight : Fin k → ℝ),
      Function.Injective point ∧ (∀ j, point j ∈ Set.range node) ∧
      (∀ j, 0 < weight j) ∧
      ∀ f : X → ℝ, ∑ j, weight j * f (point j) = ∑ i, w i * f (node i) := by
  classical
  let support : Finset X := Finset.univ.image node
  have hnode (i : Fin n) : node i ∈ support := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  let mass (x : support) : ℝ := ∑ i, if node i = x.val then w i else 0
  have hmasspos (x : support) : 0 < mass x := by
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp x.property
    have hle : w i ≤ mass x := by
      have h := Finset.single_le_sum
        (f := fun j => if node j = x.val then w j else 0)
        (fun j _ => by dsimp; split; exact (hw j).le; exact le_rfl) (Finset.mem_univ i)
      simpa only [hi, if_true, mass] using h
    exact (hw i).trans_le hle
  have hmerge (f : X → ℝ) :
      ∑ x : support, mass x * f x.val = ∑ i, w i * f (node i) := by
    simp only [mass, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    let xi : support := ⟨node i, hnode i⟩
    rw [Finset.sum_eq_single xi]
    · simp [xi]
    · intro x _ hne
      have hval : node i ≠ x.val := by
        intro heq
        apply hne
        exact Subtype.ext heq.symm
      simp [hval]
    · simp
  let e : Fin support.card ≃ support := by simpa using (Fintype.equivFin support).symm
  refine ⟨support.card, ?_, (fun j => (e j).val), (fun j => mass (e j)), ?_, ?_, ?_, ?_⟩
  · exact (Finset.card_image_le).trans (by simp)
  · exact Subtype.val_injective.comp e.injective
  · intro j
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (e j).property
    exact ⟨i, hi⟩
  · intro j
    exact hmasspos (e j)
  · intro f
    exact (Equiv.sum_comp e (fun x => mass x * f x.val)).trans (hmerge f)

end RandomizedFO2003
