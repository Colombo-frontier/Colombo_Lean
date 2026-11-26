import GradientHessian.Hierarchy

/-!
# Exact frontier truncation with arbitrary completed predecessors

Retiring a child discloses its data; it does not force its port to one at an
arbitrary selected point. The identities below retain every earlier weighted
term. Only the first still-hidden port is set to zero. The conclusions concern
the literal scalar and its actual first and second Frechet derivatives.
-/

noncomputable section
namespace GradientHessian.FrontierTruncation

open Filter
open scoped BigOperators Topology

theorem weighted_prefix {b k : ℕ} (hk : k < b) (port payload : ℕ → ℝ)
    (hzero : port k = 0) :
    (∑ i ∈ Finset.range b, Selectors.weight port i * payload i) =
      (∑ i ∈ Finset.range k, Selectors.weight port i * payload i) +
        Selectors.prefixProduct port k * payload k := by
  have hsum : (∑ i ∈ Finset.range b, Selectors.weight port i * payload i) =
      ∑ i ∈ Finset.range (k+1), Selectors.weight port i * payload i := by
    symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro i _ hi
    have hki : k < i := by
      have : ¬i < k+1 := by simpa only [Finset.mem_range] using hi
      omega
    rw [Selectors.weight_zero_after hzero hki, zero_mul]
  rw [hsum, Finset.sum_range_succ]
  simp [Selectors.weight, hzero]

variable {Z : Type*}

/-- Known predecessor terms, the prefix-weighted active child, and all self
terms. This expression does not inspect any later child or later parent port. -/
def frontierScalar (b k : ℕ) (baseline : Z → ℝ) (spacing : ℝ)
    (child childPort parentSelf incoming parentPort : ℕ → Z → ℝ) (z : Z) : ℝ :=
  baseline z +
    (∑ i ∈ Finset.range k, Selectors.weight (fun j => parentPort j z) i *
      (child i z - baseline z - i*spacing - incoming i z*childPort i z)) +
    Selectors.prefixProduct (fun j => parentPort j z) k *
      (child k z - baseline z - k*spacing - incoming k z*childPort k z) +
    ∑ i ∈ Finset.range b, parentSelf i z

theorem node_eq_frontier (b k : ℕ) (baseline : Z → ℝ) (spacing : ℝ)
    (child childPort parentSelf incoming parentPort : ℕ → Z → ℝ) (z : Z)
    (hk : k < b) (hzero : parentPort k z = 0) :
    Hierarchy.nodeScalar b baseline spacing child childPort parentSelf incoming parentPort z =
      frontierScalar b k baseline spacing child childPort parentSelf incoming parentPort z := by
  have hterminal : Selectors.prefixProduct (fun j => parentPort j z) b = 0 :=
    Finset.prod_eq_zero (Finset.mem_range.mpr hk) hzero
  unfold Hierarchy.nodeScalar frontierScalar
  rw [weighted_prefix hk _ _ hzero, hterminal]
  ring

/-- The active incoming coefficient is removable only when its own child
port vanishes. Earlier incoming terms remain present. -/
def frontierWithoutIncoming (b k : ℕ) (baseline : Z → ℝ) (spacing : ℝ)
    (child childPort parentSelf incoming parentPort : ℕ → Z → ℝ) (z : Z) : ℝ :=
  baseline z +
    (∑ i ∈ Finset.range k, Selectors.weight (fun j => parentPort j z) i *
      (child i z - baseline z - i*spacing - incoming i z*childPort i z)) +
    Selectors.prefixProduct (fun j => parentPort j z) k *
      (child k z - baseline z - k*spacing) +
    ∑ i ∈ Finset.range b, parentSelf i z

theorem frontier_eq_withoutIncoming (b k : ℕ) (baseline : Z → ℝ) (spacing : ℝ)
    (child childPort parentSelf incoming parentPort : ℕ → Z → ℝ) (z : Z)
    (hchild : childPort k z = 0) :
    frontierScalar b k baseline spacing child childPort parentSelf incoming parentPort z =
      frontierWithoutIncoming b k baseline spacing child childPort parentSelf incoming parentPort z := by
  simp only [frontierScalar, frontierWithoutIncoming, hchild, mul_zero, sub_zero]

theorem node_eq_withoutIncoming (b k : ℕ) (baseline : Z → ℝ) (spacing : ℝ)
    (child childPort parentSelf incoming parentPort : ℕ → Z → ℝ) (z : Z)
    (hk : k < b) (hparent : parentPort k z = 0) (hchild : childPort k z = 0) :
    Hierarchy.nodeScalar b baseline spacing child childPort parentSelf incoming parentPort z =
      frontierWithoutIncoming b k baseline spacing child childPort parentSelf incoming parentPort z :=
  (node_eq_frontier b k baseline spacing child childPort parentSelf incoming parentPort z hk hparent).trans
    (frontier_eq_withoutIncoming b k baseline spacing child childPort parentSelf incoming parentPort z hchild)

variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]

omit [NormedSpace ℝ Z] in
theorem node_frontier_eventuallyEq (b k : ℕ) (baseline : Z → ℝ) (spacing : ℝ)
    (child childPort parentSelf incoming parentPort : ℕ → Z → ℝ) (z : Z)
    (hk : k < b) (hzero : parentPort k =ᶠ[𝓝 z] fun _ => 0) :
    Hierarchy.nodeScalar b baseline spacing child childPort parentSelf incoming parentPort =ᶠ[𝓝 z]
      frontierScalar b k baseline spacing child childPort parentSelf incoming parentPort := by
  filter_upwards [hzero] with x hx
  exact node_eq_frontier b k baseline spacing child childPort parentSelf incoming parentPort x hk hx

theorem node_frontier_richJet (b k : ℕ) (baseline : Z → ℝ) (spacing : ℝ)
    (child childPort parentSelf incoming parentPort : ℕ → Z → ℝ) (z : Z)
    (hk : k < b) (hzero : parentPort k =ᶠ[𝓝 z] fun _ => 0) :
    JetLocality.richJet
      (Hierarchy.nodeScalar b baseline spacing child childPort parentSelf incoming parentPort) z =
    JetLocality.richJet
      (frontierScalar b k baseline spacing child childPort parentSelf incoming parentPort) z :=
  JetLocality.richJet_congr_of_eventuallyEq
    (node_frontier_eventuallyEq b k baseline spacing child childPort parentSelf incoming parentPort z hk hzero)

theorem node_frontier_ordinaryJet (b k : ℕ) (baseline : Z → ℝ) (spacing : ℝ)
    (child childPort parentSelf incoming parentPort : ℕ → Z → ℝ) (z : Z)
    (hk : k < b) (hzero : parentPort k =ᶠ[𝓝 z] fun _ => 0) :
    JetLocality.ordinaryJet
      (Hierarchy.nodeScalar b baseline spacing child childPort parentSelf incoming parentPort) z =
    JetLocality.ordinaryJet
      (frontierScalar b k baseline spacing child childPort parentSelf incoming parentPort) z :=
  JetLocality.ordinaryJet_congr_of_eventuallyEq
    (node_frontier_eventuallyEq b k baseline spacing child childPort parentSelf incoming parentPort z hk hzero)

theorem node_withoutIncoming_richJet (b k : ℕ) (baseline : Z → ℝ) (spacing : ℝ)
    (child childPort parentSelf incoming parentPort : ℕ → Z → ℝ) (z : Z)
    (hk : k < b) (hparent : parentPort k =ᶠ[𝓝 z] fun _ => 0)
    (hchild : childPort k =ᶠ[𝓝 z] fun _ => 0) :
    JetLocality.richJet
      (Hierarchy.nodeScalar b baseline spacing child childPort parentSelf incoming parentPort) z =
    JetLocality.richJet
      (frontierWithoutIncoming b k baseline spacing child childPort parentSelf incoming parentPort) z := by
  apply JetLocality.richJet_congr_of_eventuallyEq
  filter_upwards [hparent, hchild] with x hp hc
  exact node_eq_withoutIncoming b k baseline spacing child childPort parentSelf incoming parentPort x hk hp hc

end GradientHessian.FrontierTruncation
