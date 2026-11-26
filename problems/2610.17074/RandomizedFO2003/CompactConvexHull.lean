import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Topology
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

namespace RandomizedFO2003

open Set
open scoped BigOperators

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Carathéodory with a fixed natural-number index type and an explicit ambient
dimension bound. This form is convenient for compactness and spectral designs. -/
theorem finite_convex_representation {s : Set E} {x : E} (hx : x ∈ convexHull ℝ s) :
    ∃ n : ℕ, n ≤ Module.finrank ℝ E + 1 ∧
      ∃ (z : Fin n → E) (w : Fin n → ℝ),
        (∀ i, z i ∈ s) ∧ (∀ i, 0 < w i) ∧
        ∑ i, w i = 1 ∧ ∑ i, w i • z i = x := by
  classical
  obtain ⟨ι, hι, z, w, hz, hind, hw, hsum, hrepr⟩ :=
    eq_pos_convex_span_of_mem_convexHull hx
  letI : Fintype ι := hι
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, ?_, z ∘ e.symm, w ∘ e.symm, ?_, ?_, ?_, ?_⟩
  · exact hind.card_le_finrank_succ.trans (Nat.add_le_add_right (Submodule.finrank_le _) 1)
  · intro i
    exact hz ⟨e.symm i, rfl⟩
  · intro i
    exact hw (e.symm i)
  · simpa only [Function.comp_apply, Equiv.sum_comp] using hsum
  · change (∑ i, (fun j => w j • z j) (e.symm i)) = x
    exact (Equiv.sum_comp e.symm (fun j => w j • z j)).trans hrepr

private abbrev ConvexData (s : Set E) (n : ℕ) :=
  ↥(stdSimplex ℝ (Fin n)) × (Fin n → s)

private def convexValue {s : Set E} {n : ℕ} (p : ConvexData s n) : E :=
  ∑ i, p.1.val i • (p.2 i).val

omit [FiniteDimensional ℝ E] in
private theorem continuous_convexValue {s : Set E} {n : ℕ} :
    Continuous (convexValue : ConvexData s n → E) := by
  unfold convexValue
  apply continuous_finset_sum
  intro i _
  exact ((continuous_apply i).comp (continuous_subtype_val.comp continuous_fst)).smul
    (continuous_subtype_val.comp ((continuous_apply i).comp continuous_snd))

omit [FiniteDimensional ℝ E] in
private theorem convexValue_mem {s : Set E} {n : ℕ} (p : ConvexData s n) :
    convexValue p ∈ convexHull ℝ s := by
  apply (convex_convexHull ℝ s).sum_mem
  · intro i _
    exact p.1.property.1 i
  · exact p.1.property.2
  · intro i _
    exact subset_convexHull ℝ s (p.2 i).property

/-- In finite dimension the convex hull of a compact set is compact. This is
proved through finite convex combinations, so no coefficient compactness for
polynomial minimizers is assumed. -/
theorem compact_convexHull {s : Set E} (hs : IsCompact s) :
    IsCompact (convexHull ℝ s) := by
  classical
  letI : CompactSpace s := isCompact_iff_compactSpace.mp hs
  have hrepr : convexHull ℝ s =
      ⋃ n : Fin (Module.finrank ℝ E + 2),
        Set.range (convexValue : ConvexData s n.val → E) := by
    ext x
    constructor
    · intro hx
      obtain ⟨n, hn, z, w, hz, hw, hsum, hrepr⟩ := finite_convex_representation hx
      refine Set.mem_iUnion.mpr ⟨⟨n, by omega⟩, ?_⟩
      refine ⟨(⟨w, ⟨fun i => (hw i).le, hsum⟩⟩, fun i => ⟨z i, hz i⟩), ?_⟩
      exact hrepr
    · intro hx
      obtain ⟨n, p, rfl⟩ := Set.mem_iUnion.mp hx
      exact convexValue_mem p
  rw [hrepr]
  apply isCompact_iUnion
  intro n
  exact isCompact_range continuous_convexValue

end RandomizedFO2003
