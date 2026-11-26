import Nonsmooth.SupportSelectionKernel

open MeasureTheory ProbabilityTheory Set
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem supportWinner_iff_loser_regions {k : ℕ} [Nonempty (Fin k)] (a : Fin k → E) (u : E) (w : Fin k) :
    supportWinner a u = w ↔
      ∀ i, a i ∈ Prod.mk (w, ⟪a w, u⟫_ℝ) ⁻¹' supportLoserRegion u i := by
  classical
  constructor
  · intro hw
    have h := (supportWinner_eq_iff a u w).mp hw
    intro i
    change ⟪a i, u⟫_ℝ ≤ ⟪a w, u⟫_ℝ ∧ (¬i < w ∨ ⟪a i, u⟫_ℝ < ⟪a w, u⟫_ℝ)
    refine ⟨h.1 ▸ finiteSupport_ge a u i, ?_⟩
    by_cases hi : i < w
    · exact Or.inr (h.1 ▸ h.2 i hi)
    · exact Or.inl hi
  · intro h
    have hv : finiteSupport a u = ⟪a w, u⟫_ℝ := by
      apply le_antisymm ?_ (finiteSupport_ge a u w)
      apply (Finset.sup'_le_iff _ _).mpr
      intro i _
      exact (h i).1
    apply (supportWinner_eq_iff a u w).mpr
    refine ⟨hv, ?_⟩
    intro i hi
    rw [hv]
    exact (h i).2.resolve_left (not_not_intro hi)

theorem support_selection_rectangle {k : ℕ} [Nonempty (Fin k)]
    (a : Fin k → E) (u : E) (w : Fin k) (D : Set ℝ) (A : Fin k → Set E) :
    (supportWinner a u = w ∧ finiteSupport a u ∈ D ∧ ∀ i, a i ∈ A i) ↔
      a w ∈ A w ∧ ⟪a w, u⟫_ℝ ∈ D ∧
        ∀ i, i ≠ w → a i ∈ A i ∩ (Prod.mk (w, ⟪a w, u⟫_ℝ) ⁻¹' supportLoserRegion u i) := by
  classical
  constructor
  · rintro ⟨hw, hy, hA⟩
    have hregions := (supportWinner_iff_loser_regions a u w).mp hw
    have he := supportWinner_attained a u
    rw [hw] at he
    exact ⟨hA w, he ▸ hy, fun i _ => ⟨hA i, hregions i⟩⟩
  · rintro ⟨hAw, hy, hrest⟩
    have hregions : ∀ i, a i ∈ Prod.mk (w, ⟪a w, u⟫_ℝ) ⁻¹' supportLoserRegion u i := by
      intro i
      by_cases hi : i = w
      · subst i
        simp [supportLoserRegion]
      · exact (hrest i hi).2
    have hw := (supportWinner_iff_loser_regions a u w).mpr hregions
    have he := supportWinner_attained a u
    rw [hw] at he
    refine ⟨hw, he.symm ▸ hy, ?_⟩
    intro i
    by_cases hi : i = w
    · simpa only [hi] using hAw
    · exact (hrest i hi).1

theorem support_selection_insertNth {n : ℕ} (w : Fin (n + 1)) (z : E) (b : Fin n → E)
    (u : E) (D : Set ℝ) (A : Fin (n + 1) → Set E) :
    (supportWinner (w.insertNth z b) u = w ∧ finiteSupport (w.insertNth z b) u ∈ D ∧
      ∀ i : Fin (n + 1), (w.insertNth z b : Fin (n + 1) → E) i ∈ A i) ↔
      z ∈ A w ∧ ⟪z, u⟫_ℝ ∈ D ∧
        b ∈ Set.univ.pi (fun j => A (w.succAbove j) ∩
          (Prod.mk (w, ⟪z, u⟫_ℝ) ⁻¹' supportLoserRegion u (w.succAbove j))) := by
  rw [support_selection_rectangle]
  simp only [Fin.insertNth_apply_same]
  constructor
  · rintro ⟨hz, hy, hrest⟩
    refine ⟨hz, hy, ?_⟩
    intro j _
    simpa only [Fin.insertNth_apply_succAbove] using hrest (w.succAbove j) (w.succAbove_ne j)
  · rintro ⟨hz, hy, hb⟩
    refine ⟨hz, hy, ?_⟩
    intro i
    refine Fin.succAboveCases w ?_ (fun j => ?_) i
    · intro hi
      exact (hi rfl).elim
    · intro _
      simpa only [Fin.insertNth_apply_succAbove] using hb j (mem_univ j)

end
end Nonsmooth
