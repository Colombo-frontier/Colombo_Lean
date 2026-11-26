import Mathlib

/-!
# Orthogonal frame selection for deterministic transcripts

This module proves the finite-dimensional existence step used in
`source/main.tex`, lines 1028-1038. A unit vector exists orthogonal to any
list of fewer constraints than the ambient real dimension. The list can
contain dependent or repeated vectors; independence is not assumed.

This is a genuine linear-algebra construction theorem. It does not by
itself prove that the potential's complete jet is unaffected by adding
this vector. That remaining bridge requires the concrete scalar gates.
-/

namespace MinimaxAudit.Frame

open Module Submodule

/-- A proper finite list of constraints leaves a unit vector in their
orthogonal complement. -/
theorem exists_unit_orthogonal_finset
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (constraints : Finset E)
    (hsize : constraints.card < finrank ℝ E) :
    ∃ u : E, ‖u‖ = 1 ∧ ∀ x ∈ constraints, inner ℝ u x = 0 := by
  classical
  let K : Submodule ℝ E := span ℝ (constraints : Set E)
  have hdim : finrank ℝ K < finrank ℝ E :=
    (finrank_span_finset_le_card constraints).trans_lt hsize
  have hadd := K.finrank_add_finrank_orthogonal
  have hpos : 0 < finrank ℝ Kᗮ := by omega
  obtain ⟨v, hv⟩ := (Module.finrank_pos_iff_exists_ne_zero).mp hpos
  have hvcoe : (v : E) ≠ 0 := by
    intro hz
    apply hv
    exact Subtype.ext hz
  let u : E := NormedSpace.normalize (v : E)
  have hu : u ∈ Kᗮ := by
    exact Kᗮ.smul_mem ‖(v : E)‖⁻¹ v.property
  refine ⟨u, NormedSpace.norm_normalize hvcoe, ?_⟩
  intro x hx
  apply Submodule.inner_left_of_mem_orthogonal (K := K) _ hu
  exact Submodule.subset_span hx

/-- List form: the upper bound counts vectors without having to deduplicate
query points or prove independence of the constraints. -/
theorem exists_unit_orthogonal_list
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (constraints : List E)
    (hsize : constraints.length < finrank ℝ E) :
    ∃ u : E, ‖u‖ = 1 ∧ ∀ x ∈ constraints, inner ℝ u x = 0 := by
  classical
  obtain ⟨u, hu, horth⟩ := exists_unit_orthogonal_finset constraints.toFinset
    (constraints.toFinset_card_le.trans_lt hsize)
  exact ⟨u, hu, fun x hx => horth x (by simpa using hx)⟩

/-- Add one new direction, indexed by `none`, to an existing frame indexed
by `some i`. Option indexing avoids any dependence on a specific Fin cast. -/
def extendFrame {ι E : Type*} (frame : ι → E) (u : E) : Option ι → E
  | none => u
  | some i => frame i

/-- A unit vector orthogonal to an old orthonormal frame produces a genuine
larger orthonormal frame. -/
theorem orthonormal_extendFrame
    {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (frame : ι → E) (hframe : Orthonormal ℝ frame)
    (u : E) (hu : ‖u‖ = 1) (horth : ∀ i, inner ℝ u (frame i) = 0) :
    Orthonormal ℝ (extendFrame frame u) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  cases i with
  | none =>
    cases j with
    | none => simp [extendFrame, hu]
    | some j => simp [extendFrame, horth j]
  | some i =>
    cases j with
    | none => simp [extendFrame, real_inner_comm, horth i]
    | some j => simpa [extendFrame] using (orthonormal_iff_ite.mp hframe i j)

/-- Extend an actual finite orthonormal frame while avoiding an additional
list of query constraints. Repetition or dependence of queries is allowed. -/
theorem exists_orthonormal_extension_avoiding
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {k : ℕ} (frame : Fin k → E) (hframe : Orthonormal ℝ frame)
    (queries : List E) (hsize : k + queries.length < finrank ℝ E) :
    ∃ u : E, Orthonormal ℝ (extendFrame frame u) ∧
      ∀ q ∈ queries, inner ℝ u q = 0 := by
  obtain ⟨u, hu, horth⟩ := exists_unit_orthogonal_list
    (List.ofFn frame ++ queries) (by simpa using hsize)
  refine ⟨u, orthonormal_extendFrame frame hframe u hu ?_, ?_⟩
  · intro i
    apply horth (frame i)
    simp
  · intro q hq
    exact horth q (by simp [hq])

/-- At round t the old frame contributes t−1 vectors and the transcript
contributes t query vectors. The dimension 2N+2 leaves room whenever t≤N. -/
theorem round_constraint_count (N t : ℕ) (ht : t ≤ N) :
    (t - 1) + t < 2 * N + 2 := by omega

/-- The final selection avoids N frame vectors, N queries, and one
arbitrary output vector. -/
theorem final_constraint_count (N : ℕ) :
    N + N + 1 < 2 * N + 2 := by omega

/-- Concrete selection at an intermediate deterministic round. -/
theorem exists_round_hidden_direction
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (N t : ℕ) (ht : t ≤ N) (hdim : finrank ℝ E = 2 * N + 2)
    (previous queries : List E)
    (hprevious : previous.length = t - 1) (hqueries : queries.length = t) :
    ∃ u : E, ‖u‖ = 1 ∧
      (∀ x ∈ previous, inner ℝ u x = 0) ∧
      (∀ x ∈ queries, inner ℝ u x = 0) := by
  obtain ⟨u, hu, horth⟩ := exists_unit_orthogonal_list
    (previous ++ queries) (by
      simpa [hprevious, hqueries, hdim] using round_constraint_count N t ht)
  refine ⟨u, hu, ?_, ?_⟩
  · intro x hx
    exact horth x (by simp [hx])
  · intro x hx
    exact horth x (by simp [hx])

/-- Concrete final deterministic selection in the paper's dimension.
The output need not be one of the queried points. -/
theorem exists_final_hidden_direction
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (N : ℕ) (hdim : finrank ℝ E = 2 * N + 2)
    (previous queries : List E)
    (hprevious : previous.length = N) (hqueries : queries.length = N)
    (output : E) :
    ∃ u : E, ‖u‖ = 1 ∧
      (∀ x ∈ previous, inner ℝ u x = 0) ∧
      (∀ x ∈ queries, inner ℝ u x = 0) ∧
      inner ℝ u output = 0 := by
  obtain ⟨u, hu, horth⟩ := exists_unit_orthogonal_list
    (previous ++ queries ++ [output]) (by simp [hprevious, hqueries, hdim]; omega)
  refine ⟨u, hu, ?_, ?_, ?_⟩
  · intro x hx
    exact horth x (by simp [hx])
  · intro x hx
    exact horth x (by simp [hx])
  · exact horth output (by simp)

end MinimaxAudit.Frame
