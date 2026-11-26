import HeavyTail.MirrorDescent
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# A measurable approximate first-order optimizer on the finite simplex

The selected point is the first point of a fixed dense sequence passing every
vertex first-order test. Existence is derived from compact minimization and
continuity of the genuine derivative. No residual bound or measurable
optimizer is assumed in the selector theorem.
-/

noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped BigOperators

namespace HeavyTail

variable {ι : Type*} [Fintype ι] [Nonempty ι]

abbrev SimplexPoint (ι : Type*) [Fintype ι] := {w : ι → ℝ // w ∈ stdSimplex ℝ ι}

instance simplexPoint_nonempty : Nonempty (SimplexPoint ι) := by
  classical
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact ⟨⟨Pi.single i 1, single_mem_stdSimplex ℝ i⟩⟩

/-- Fixed independently of all observed losses and randomness. -/
def simplexDensePoint (n : ℕ) : SimplexPoint ι := denseSeq (SimplexPoint ι) n

theorem simplexDensePoint_dense : DenseRange (simplexDensePoint (ι := ι)) :=
  denseRange_denseSeq _

def simplexVertexTests (d : (ι → ℝ) →L[ℝ] ℝ) (y : ι → ℝ) (ε : ℝ) : Prop := by
  classical
  exact ∀ i, -ε < d (Pi.single i 1 - y)

omit [Nonempty ι] in
/-- Vertex tests control every comparator, including boundary points. -/
theorem simplex_vertex_tests_first_order {d : (ι → ℝ) →L[ℝ] ℝ}
    {y q : ι → ℝ} {ε : ℝ} (hq : q ∈ stdSimplex ℝ ι)
    (htest : simplexVertexTests d y ε) : -ε ≤ d (q - y) := by
  classical
  have hreconstruct : (∑ i, q i • (Pi.single i 1 : ι → ℝ)) = q := by
    ext j
    simp [Pi.single_apply, Pi.smul_apply]
  have hlinear : (∑ i, q i * d (Pi.single i 1)) = d q := by
    calc
      _ = d (∑ i, q i • (Pi.single i 1 : ι → ℝ)) := by
        simp only [map_sum, map_smul, smul_eq_mul]
      _ = _ := by rw [hreconstruct]
  have hsum : (∑ i, q i * d (Pi.single i 1 - y)) = d (q - y) := by
    simp only [map_sub, mul_sub, Finset.sum_sub_distrib, hlinear,
      ← Finset.sum_mul, hq.2, one_mul]
  have h := Finset.sum_le_sum (fun i (_hi : i ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (htest i).le (hq.1 i))
  rw [hsum, ← Finset.sum_mul, hq.2, one_mul] at h
  exact h

/-- Compact minimization and derivative continuity imply a successful dense candidate. -/
theorem exists_dense_simplex_vertex_tests
    (F : (ι → ℝ) → ℝ) (dF : (ι → ℝ) → (ι → ℝ) →L[ℝ] ℝ)
    (hderiv : ∀ w ∈ stdSimplex ℝ ι, HasFDerivWithinAt F (dF w) (stdSimplex ℝ ι) w)
    (hcont : ContinuousOn dF (stdSimplex ℝ ι)) {ε : ℝ} (hε : 0 < ε) :
    ∃ n, simplexVertexTests (dF (simplexDensePoint (ι := ι) n))
      (simplexDensePoint (ι := ι) n) ε := by
  classical
  obtain ⟨y, hy, hmin⟩ := (isCompact_stdSimplex ι).exists_isMinOn
    (show (stdSimplex ℝ ι).Nonempty from
      ⟨(simplexDensePoint (ι := ι) 0).val, (simplexDensePoint (ι := ι) 0).property⟩)
    (fun w hw => (hderiv w hw).continuousWithinAt)
  let U : Set (SimplexPoint ι) := {w | simplexVertexTests (dF w) w ε}
  have hU : IsOpen U := by
    change IsOpen {w : SimplexPoint ι | ∀ i, -ε < dF w.val (Pi.single i 1 - w.val)}
    simp only [setOf_forall]
    apply isOpen_iInter_of_finite
    intro i
    exact isOpen_lt continuous_const
      (hcont.restrict.clm_apply (continuous_const.sub continuous_subtype_val))
  have hyU : (⟨y, hy⟩ : SimplexPoint ι) ∈ U := by
    change ∀ i, -ε < dF y (Pi.single i 1 - y)
    intro i
    have hi := constrained_minimum_first_order (convex_stdSimplex ℝ ι) hy
      (single_mem_stdSimplex ℝ i) hmin (hderiv y hy)
    exact (neg_neg_of_pos hε).trans_le hi
  exact simplexDensePoint_dense.exists_mem_open hU ⟨⟨y, hy⟩, hyU⟩

/-- Actual measurable selection with a uniform variational-inequality residual. -/
theorem exists_measurable_simplex_first_order_optimizer
    {P : Type*} [MeasurableSpace P]
    (F : P → (ι → ℝ) → ℝ) (dF : P → (ι → ℝ) → (ι → ℝ) →L[ℝ] ℝ)
    (hderiv : ∀ p w, w ∈ stdSimplex ℝ ι →
      HasFDerivWithinAt (F p) (dF p w) (stdSimplex ℝ ι) w)
    (hcont : ∀ p, ContinuousOn (dF p) (stdSimplex ℝ ι))
    (hmeas : ∀ w ∈ stdSimplex ℝ ι, Measurable (fun p => dF p w))
    (ε : P → ℝ) (hεmeas : Measurable ε) (hε : ∀ p, 0 < ε p) :
    ∃ update : P → (ι → ℝ), Measurable update ∧
      (∀ p, update p ∈ stdSimplex ℝ ι) ∧
      ∀ p q, q ∈ stdSimplex ℝ ι → -ε p ≤ dF p (update p) (q - update p) := by
  classical
  let pred : ℕ → P → Prop := fun n p =>
    simplexVertexTests (dF p (simplexDensePoint (ι := ι) n)) (simplexDensePoint (ι := ι) n) (ε p)
  have hex (p : P) : ∃ n, pred n p :=
    exists_dense_simplex_vertex_tests (F p) (dF p) (hderiv p) (hcont p) (hε p)
  let update : P → (ι → ℝ) := fun p => simplexDensePoint (ι := ι) (Nat.find (hex p))
  refine ⟨update, ?_, (fun p => (simplexDensePoint (ι := ι) (Nat.find (hex p))).property), ?_⟩
  · change Measurable (fun p => (simplexDensePoint (ι := ι) (Nat.find (hex p))).val)
    refine Measurable.find (f := fun n (_p : P) => (simplexDensePoint (ι := ι) n).val)
      (p := pred) (fun _ => measurable_const) ?_ hex
    intro n
    change MeasurableSet {p | ∀ i, -ε p <
      dF p (simplexDensePoint (ι := ι) n).val (Pi.single i 1 - (simplexDensePoint (ι := ι) n).val)}
    simp only [setOf_forall]
    apply MeasurableSet.iInter
    intro i
    exact measurableSet_lt hεmeas.neg
      ((hmeas _ (simplexDensePoint (ι := ι) n).property).apply_continuousLinearMap
        (Pi.single i 1 - (simplexDensePoint (ι := ι) n).val))
  · intro p q hq
    exact simplex_vertex_tests_first_order hq (Nat.find_spec (hex p))

section ApproximateMirror

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem approximate_mirror_update {H : E → ℝ} {dH : E → E →L[ℝ] ℝ}
    (L : E →L[ℝ] ℝ) {x y q : E} {ε : ℝ}
    (hfirst : -ε ≤ (L + dH y - dH x) (q - y)) :
    bregmanDivergence H dH q y ≤ bregmanDivergence H dH q x +
      L q + mirrorStability H dH L x y + ε := by
  have hid := bregman_three_point_identity H dH q x y
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply, map_sub] at hfirst hid
  unfold mirrorStability
  linarith

theorem approximate_mirror_telescope {H : E → ℝ} {dH : E → E →L[ℝ] ℝ}
    {x : ℕ → E} {L : ℕ → E →L[ℝ] ℝ} {q : E} {ε : ℝ}
    (hfirst : ∀ k, -ε ≤ (L k + dH (x (k + 1)) - dH (x k)) (q - x (k + 1))) (n : ℕ) :
    bregmanDivergence H dH q (x n) ≤ bregmanDivergence H dH q (x 0) +
      (∑ k ∈ Finset.range n, (L k q + mirrorStability H dH (L k) (x k) (x (k + 1)))) + n * ε := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep := approximate_mirror_update (H := H) (L n) (hfirst n)
    rw [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
    linarith

theorem approximate_mirror_regret {S : Set E} {H : E → ℝ} {dH : E → E →L[ℝ] ℝ}
    {x : ℕ → E} {L : ℕ → E →L[ℝ] ℝ} {q : E} {ε : ℝ}
    (hH : ConvexOn ℝ S H) (hx : ∀ k, x k ∈ S) (hq : q ∈ S)
    (hd : ∀ w ∈ S, HasFDerivWithinAt H (dH w) S w)
    (hfirst : ∀ k, -ε ≤ (L k + dH (x (k + 1)) - dH (x k)) (q - x (k + 1))) (n : ℕ) :
    -(∑ k ∈ Finset.range n, L k q) ≤ bregmanDivergence H dH q (x 0) +
      (∑ k ∈ Finset.range n, mirrorStability H dH (L k) (x k) (x (k + 1))) + n * ε := by
  have htel := approximate_mirror_telescope (H := H) hfirst n
  have hpos := bregmanDivergence_nonneg hH (hx n) hq (hd _ (hx n))
  rw [Finset.sum_add_distrib] at htel
  linarith

end ApproximateMirror
end HeavyTail
