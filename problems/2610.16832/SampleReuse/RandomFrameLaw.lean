import SampleReuse.RandomFrameAdaptive

noncomputable section
namespace SampleReuse.RandomFrame

open MeasureTheory RandomizedFO2003 Rotations
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
variable {ι κ : Type*}

/-- An orthonormal frame, obtained by rotating a fixed orthonormal family with
an actual Haar-distributed orthogonal operator. -/
def frame (e : ι → E) (he : Orthonormal ℝ e) (U : Rotation E) :
    {v : ι → E // Orthonormal ℝ v} :=
  ⟨fun i => isometry E U (e i), he.comp_linearIsometryEquiv (isometry E U)⟩

theorem measurable_frame (e : ι → E) (he : Orthonormal ℝ e) :
    Measurable (frame e he) :=
  (measurable_pi_lambda _ (fun i => measurable_orbit E (e i))).subtype_mk

def frameLaw (e : ι → E) (he : Orthonormal ℝ e) :
    Measure {v : ι → E // Orthonormal ℝ v} := (haarLaw E).map (frame e he)

instance frameLaw_probability (e : ι → E) (he : Orthonormal ℝ e) :
    IsProbabilityMeasure (frameLaw e he) :=
  isProbabilityMeasure_map (measurable_frame e he).aemeasurable

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
theorem hidden_mem_orthogonal (e : ι → E) (he : Orthonormal ℝ e)
    (a : κ → ι) (j : ι) (hj : ∀ k, a k ≠ j) :
    e j ∈ (Submodule.span ℝ (Set.range (e ∘ a)))ᗮ := by
  apply (Submodule.mem_orthogonal _ _).mpr
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact he.inner_eq_zero (hj k)
  | zero => simp
  | add x y hx hy ihx ihy => simp only [inner_add_left, ihx, ihy, add_zero]
  | smul c x hx ih => simp only [inner_smul_left, ih, mul_zero]

/-- A query may be any measurable function of the revealed columns. Its
projection onto each unrevealed column has a tail in the remaining dimension. -/
theorem revealed_query_tail [Fintype κ] (e : ι → E) (he : Orthonormal ℝ e)
    (a : κ → ι) (ha : Function.Injective a) (j : ι) (hj : ∀ k, a k ≠ j)
    (q : (κ → E) → E) (hq : Measurable q) {R t : ℝ}
    (hR : 0 < R) (ht : 0 < t) (hbound : ∀ z, ‖q z‖ ≤ R) :
    (haarLaw E).real {U | t ≤ |⟪q (fun k => isometry E U (e (a k))),
        isometry E U (e j)⟫_ℝ|} ≤
      2 * Real.exp (-((Module.finrank ℝ E - Fintype.card κ : ℕ) : ℝ) * t ^ 2 /
        (2 * R ^ 2)) := by
  let L := Submodule.span ℝ (Set.range (e ∘ a))
  let v : Lᗮ := ⟨e j, hidden_mem_orthogonal e he a j hj⟩
  have hv : ‖v‖ = 1 := he.norm_eq_one j
  let Q : Rotation E → E := fun U => q (fun k => isometry E U (e (a k)))
  have hQ : Measurable Q := hq.comp (measurable_pi_lambda _
    (fun k => measurable_orbit E (e (a k))))
  have hknown : ∀ U V, Q (U * extendComplement L V) = Q U := by
    intro U V
    apply congrArg q
    funext k
    exact compatibleRotation_fixed L U V ⟨e (a k), Submodule.subset_span ⟨k, rfl⟩⟩
  have hdim : Module.finrank ℝ Lᗮ = Module.finrank ℝ E - Fintype.card κ := by
    have hL : Module.finrank ℝ L = Fintype.card κ :=
      finrank_span_eq_card ((he.comp a ha).linearIndependent)
    have hsum := L.finrank_add_finrank_orthogonal
    omega
  have htail := invariant_query_projection_tail L v hv Q hQ hknown hR ht
    (fun U => hbound _)
  simpa only [hdim] using htail

/-- Queries outside the informative ball are replaced by zero only for the
probability estimate. The event below still refers to the original query. -/
def boundedQuery (R : ℝ) (x : E) : E := if ‖x‖ ≤ R then x else 0

omit [FiniteDimensional ℝ E] [InnerProductSpace ℝ E] in
theorem measurable_boundedQuery (R : ℝ) : Measurable (boundedQuery (E := E) R) := by
  apply Measurable.ite _ measurable_id measurable_const
  exact measurableSet_le measurable_norm measurable_const

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ E] in
theorem boundedQuery_norm_le {R : ℝ} (hR : 0 ≤ R) (x : E) : ‖boundedQuery R x‖ ≤ R := by
  by_cases hx : ‖x‖ ≤ R
  · simp [boundedQuery, hx]
  · simpa [boundedQuery, hx] using hR

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
theorem boundedQuery_projection_event {R t : ℝ} (ht : 0 < t) (x y : E) :
    (t ≤ |⟪boundedQuery R x, y⟫_ℝ|) ↔ (‖x‖ ≤ R ∧ t ≤ |⟪x, y⟫_ℝ|) := by
  by_cases hx : ‖x‖ ≤ R
  · simp [boundedQuery, hx]
  · simp [boundedQuery, hx, not_le_of_gt ht]

theorem revealed_query_inside_tail [Fintype κ] (e : ι → E) (he : Orthonormal ℝ e)
    (a : κ → ι) (ha : Function.Injective a) (j : ι) (hj : ∀ k, a k ≠ j)
    (q : (κ → E) → E) (hq : Measurable q) {R t : ℝ} (hR : 0 < R) (ht : 0 < t) :
    (haarLaw E).real {U | ‖q (fun k => isometry E U (e (a k)))‖ ≤ R ∧
      t ≤ |⟪q (fun k => isometry E U (e (a k))), isometry E U (e j)⟫_ℝ|} ≤
      2 * Real.exp (-((Module.finrank ℝ E - Fintype.card κ : ℕ) : ℝ) * t ^ 2 /
        (2 * R ^ 2)) := by
  have htail := revealed_query_tail e he a ha j hj
    (boundedQuery R ∘ q) ((measurable_boundedQuery R).comp hq) hR ht
    (fun z => boundedQuery_norm_le hR.le (q z))
  simpa only [Function.comp_apply, boundedQuery_projection_event ht] using htail

end SampleReuse.RandomFrame
