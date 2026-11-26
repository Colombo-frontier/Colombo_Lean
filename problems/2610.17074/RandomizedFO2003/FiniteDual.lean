import RandomizedFO2003.CompactConvexHull
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.Topology.Algebra.Module.LinearMapPiProd

/-! Finite dual designs obtained by separating a signed evaluation hull.
The coefficient space is never compactified. -/

namespace RandomizedFO2003

open Set
open scoped BigOperators

variable {X V : Type} [TopologicalSpace X]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

def signedGraph (s : Set X) (f : X → ℝ) (v : X → V) : Set (ℝ × V) :=
  (fun x => (f x, v x)) '' s ∪ (fun x => -(f x, v x)) '' s

omit [FiniteDimensional ℝ V] [NormedSpace ℝ V] in
theorem compact_signedGraph {s : Set X} (hs : IsCompact s)
    {f : X → ℝ} {v : X → V} (hf : ContinuousOn f s) (hv : ContinuousOn v s) :
    IsCompact (signedGraph s f v) :=
  (hs.image_of_continuousOn (hf.prodMk hv)).union
    (hs.image_of_continuousOn (hf.prodMk hv).neg)

/-- A uniform approximation obstruction puts a purely vertical vector in the
convex hull of the signed graph. Strict separation would construct a better
approximating linear functional and contradict the obstruction. -/
theorem approximation_point_mem_hull
    {s : Set X} (hs : IsCompact s) {f : X → ℝ} {v : X → V}
    (hf : ContinuousOn f s) (hv : ContinuousOn v s)
    {ε : ℝ} (hε : 0 < ε)
    (hgap : ∀ q : V →L[ℝ] ℝ, ∃ x ∈ s, ε ≤ |f x - q (v x)|) :
    (ε, (0 : V)) ∈ convexHull ℝ (signedGraph s f v) := by
  by_contra hnot
  obtain ⟨L, t, hLt, htL⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ _) (compact_convexHull (compact_signedGraph hs hf hv)).isClosed hnot
  have hbound (x : X) (hx : x ∈ s) : |L (f x, v x)| < t := by
    have hplus := hLt _ (subset_convexHull ℝ _ (Or.inl ⟨x, hx, rfl⟩))
    have hminus := hLt _ (subset_convexHull ℝ _ (Or.inr ⟨x, hx, rfl⟩))
    rw [map_neg] at hminus
    exact abs_lt.mpr ⟨by linarith, hplus⟩
  obtain ⟨x₀, hx₀, _⟩ := hgap 0
  have ht : 0 < t := lt_of_le_of_lt (abs_nonneg _) (hbound x₀ hx₀)
  let a : ℝ := L (1, 0)
  have hvertical (c : ℝ) : L (c, (0 : V)) = c * a := by
    have hp : (c, (0 : V)) = c • (1, (0 : V)) := by simp
    rw [hp, map_smul]
    rfl
  rw [hvertical] at htL
  have ha : 0 < a := by nlinarith
  let q : V →L[ℝ] ℝ := (-a⁻¹) • L.comp (ContinuousLinearMap.inr ℝ ℝ V)
  have hform (x : X) : L (f x, v x) = a * (f x - q (v x)) := by
    have hsplit : (f x, v x) = (f x, (0 : V)) + (0, v x) := by simp
    rw [hsplit, map_add, hvertical]
    simp only [q, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inr_apply, smul_eq_mul]
    field_simp
  obtain ⟨x, hx, herr⟩ := hgap q
  have hsmall := hbound x hx
  rw [hform, abs_mul, abs_of_pos ha] at hsmall
  have hlarge := mul_le_mul_of_nonneg_left herr ha.le
  nlinarith

/-- Jensen's quadratic inequality, written for a finite probability vector. -/
theorem probability_weighted_square {ι : Type*} [Fintype ι]
    (w y : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) :
    (∑ i, w i * y i) ^ 2 ≤ ∑ i, w i * y i ^ 2 := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul Finset.univ
    (r := fun i => w i * y i) (f := w) (g := fun i => w i * y i ^ 2)
    (fun i _ => hw i) (fun i _ => mul_nonneg (hw i) (sq_nonneg _))
    (fun i _ => by ring)
  simpa only [hsum, one_mul] using h

/-- Finite positive dual design for any finite-dimensional approximation space.
The number of nodes is at most dimension+2. Repeated nodes can subsequently be
merged without changing any of the weighted losses. -/
theorem exists_finite_dual_design
    {s : Set X} (hs : IsCompact s) {f : X → ℝ} {v : X → V}
    (hf : ContinuousOn f s) (hv : ContinuousOn v s)
    {ε : ℝ} (hε : 0 < ε)
    (hgap : ∀ q : V →L[ℝ] ℝ, ∃ x ∈ s, ε ≤ |f x - q (v x)|) :
    ∃ n : ℕ, n ≤ Module.finrank ℝ V + 2 ∧
      ∃ (node : Fin n → X) (w : Fin n → ℝ),
        (∀ i, node i ∈ s) ∧ (∀ i, 0 < w i) ∧ (∑ i, w i = 1) ∧
        ∀ q : V →L[ℝ] ℝ, ε ^ 2 ≤ ∑ i, w i * (f (node i) - q (v (node i))) ^ 2 := by
  classical
  obtain ⟨n, hn, z, w, hz, hw, hsum, hrepr⟩ := finite_convex_representation
    (approximation_point_mem_hull hs hf hv hε hgap)
  have hnodes : ∀ i, ∃ x ∈ s, z i = (f x, v x) ∨ z i = -(f x, v x) := by
    intro i
    rcases hz i with ⟨x, hx, heq⟩ | ⟨x, hx, heq⟩
    · exact ⟨x, hx, Or.inl heq.symm⟩
    · exact ⟨x, hx, Or.inr heq.symm⟩
  choose node hnode hsign using hnodes
  refine ⟨n, ?_, node, w, hnode, hw, hsum, ?_⟩
  · simpa [Module.finrank_prod, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hn
  · intro q
    let L : (ℝ × V) →L[ℝ] ℝ :=
      ContinuousLinearMap.fst ℝ ℝ V - q.comp (ContinuousLinearMap.snd ℝ ℝ V)
    have hreprL : ∑ i, w i * L (z i) = ε := by
      have h := congrArg L hrepr
      simpa [map_sum, map_smul, L] using h
    have hsquares (i : Fin n) : (L (z i)) ^ 2 =
        (f (node i) - q (v (node i))) ^ 2 := by
      rcases hsign i with h | h
      · simp [h, L]
      · simp [h, map_neg, L]
        ring
    calc
      ε ^ 2 = (∑ i, w i * L (z i)) ^ 2 := by rw [hreprL]
      _ ≤ ∑ i, w i * (L (z i)) ^ 2 := probability_weighted_square w _ (fun i => (hw i).le) hsum
      _ = ∑ i, w i * (f (node i) - q (v (node i))) ^ 2 := by simp_rw [hsquares]

end RandomizedFO2003
