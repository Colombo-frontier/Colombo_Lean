import GradientHessian.FrontierSecondJet
import GradientHessian.HigherHierarchyNode
import GradientHessian.FirstHeightFunctions

/-! Exact conversion between the literal finite-child formulas and the
natural-indexed frontier identities. Child indices affect coefficients only;
all functions below live on their original shared physical space. -/

noncomputable section
namespace GradientHessian.FiniteFrontierBridge

open SecondJetAlgebra JetLocality
open scoped BigOperators

def extend {b : ℕ} {V : Type*} [Zero V] (f : Fin b → V) (i : ℕ) : V :=
  if hi : i < b then f ⟨i,hi⟩ else 0

@[simp] theorem extend_fin {b : ℕ} {V : Type*} [Zero V] (f : Fin b → V) (i : Fin b) :
    extend f i.val = f i := by simp [extend,i.isLt]

theorem extend_apply {b : ℕ} {Z : Type*} (f : Fin b → Z → ℝ) (i : ℕ) (z : Z) :
    extend f i z = extend (fun j => f j z) i := by
  by_cases hi : i < b <;> simp [extend,hi]

theorem prefix_extend {b : ℕ} (p : Fin b → ℝ) (k : ℕ) (hk : k ≤ b) :
    Selectors.prefixProduct (extend p) k = ∏ j : Fin b, if j.val < k then p j else 1 := by
  have hs : (∏ j ∈ Finset.range k,extend p j) =
      ∏ j ∈ Finset.range k,if j < k then extend p j else 1 := by
    apply Finset.prod_congr rfl
    intro j hj
    simp [Finset.mem_range.mp hj]
  have ht : (∏ j ∈ Finset.range k,if j < k then extend p j else 1) =
      ∏ j ∈ Finset.range b,if j < k then extend p j else 1 := by
    apply Finset.prod_subset (Finset.range_mono hk)
    intro j _ hj
    simp only [Finset.mem_range] at hj
    simp [hj]
  calc
    _ = ∏ j ∈ Finset.range b,if j < k then extend p j else 1 := hs.trans ht
    _ = _ := by
      simpa only [extend_fin] using
        (Fin.prod_univ_eq_prod_range (fun j => if j < k then extend p j else 1) b).symm

theorem weight_extend {b : ℕ} (p : Fin b → ℝ) (i : Fin b) :
    Selectors.weight (extend p) i.val = InnerSelector.weight p i := by
  rw [Selectors.weight,extend_fin,prefix_extend p i.val (Nat.le_of_lt i.isLt)]
  rfl

theorem weight_extend_family {b : ℕ} {Z : Type*} (p : Fin b → Z → ℝ) (i : Fin b) (z : Z) :
    Selectors.weight (fun j => extend p j z) i.val = InnerSelector.weight (fun j => p j z) i := by
  simpa only [extend_apply] using weight_extend (fun j => p j z) i

variable {b : ℕ} {Z : Type*}

def node (baseline : Z → ℝ) (spacing : ℝ)
    (child childPort parentSelf incoming parentPort : Fin b → Z → ℝ) (z : Z) : ℝ :=
  baseline z + (∑ i,InnerSelector.weight (fun j => parentPort j z) i *
    (child i z-baseline z-i.val*spacing-incoming i z*childPort i z)) -
    b*spacing*(∏ i,parentPort i z) + ∑ i,parentSelf i z

def frontier (k : Fin b) (baseline : Z → ℝ) (spacing : ℝ)
    (child childPort parentSelf incoming parentPort : Fin b → Z → ℝ) : Z → ℝ :=
  FrontierTruncation.frontierScalar b k.val baseline spacing
    (extend child) (extend childPort) (extend parentSelf) (extend incoming) (extend parentPort)

def withoutIncoming (k : Fin b) (baseline : Z → ℝ) (spacing : ℝ)
    (child childPort parentSelf incoming parentPort : Fin b → Z → ℝ) : Z → ℝ :=
  FrontierTruncation.frontierWithoutIncoming b k.val baseline spacing
    (extend child) (extend childPort) (extend parentSelf) (extend incoming) (extend parentPort)

theorem node_eq_nat (baseline : Z → ℝ) (spacing : ℝ)
    (child childPort parentSelf incoming parentPort : Fin b → Z → ℝ) (z : Z) :
    node baseline spacing child childPort parentSelf incoming parentPort z =
      Hierarchy.nodeScalar b baseline spacing
        (extend child) (extend childPort) (extend parentSelf) (extend incoming) (extend parentPort) z := by
  have hs := Fin.sum_univ_eq_sum_range (fun i =>
    Selectors.weight (fun j => extend parentPort j z) i *
      (extend child i z-baseline z-i*spacing-extend incoming i z*extend childPort i z)) b
  simp only [weight_extend_family,extend_fin] at hs
  have hp := Fin.prod_univ_eq_prod_range (fun i => extend parentPort i z) b
  simp only [extend_fin] at hp
  have hv := Fin.sum_univ_eq_sum_range (fun i => extend parentSelf i z) b
  simp only [extend_fin] at hv
  unfold node Hierarchy.nodeScalar Selectors.prefixProduct
  rw [← hs,← hp,← hv]

variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem extend_contDiff {f : Fin b → Z → ℝ} (hf : ∀ i,ContDiff ℝ 2 (f i)) (j : ℕ) :
    ContDiff ℝ 2 (extend f j) := by
  unfold extend
  split_ifs with h
  · exact hf _
  · exact contDiff_const

theorem node_frontier_richJet (k : Fin b) (baseline : Z → ℝ) (spacing : ℝ)
    (child childPort parentSelf incoming parentPort : Fin b → Z → ℝ) (z : Z)
    (hb : ContDiff ℝ 2 baseline) (hc : ∀ i,ContDiff ℝ 2 (child i))
    (ho : ∀ i,ContDiff ℝ 2 (childPort i)) (hs : ∀ i,ContDiff ℝ 2 (parentSelf i))
    (hi : ∀ i,ContDiff ℝ 2 (incoming i)) (hp : ∀ i,ContDiff ℝ 2 (parentPort i))
    (hz : ZeroSecondJet (parentPort k) z) :
    richJet (node baseline spacing child childPort parentSelf incoming parentPort) z =
      richJet (frontier k baseline spacing child childPort parentSelf incoming parentPort) z := by
  rw [funext (node_eq_nat baseline spacing child childPort parentSelf incoming parentPort)]
  exact FrontierSecondJet.node_frontier_richJet_of_zeroSecondJet b k.val baseline spacing
    _ _ _ _ _ z k.isLt hb (extend_contDiff hc) (extend_contDiff ho) (extend_contDiff hs)
    (extend_contDiff hi) (extend_contDiff hp) (by simpa only [extend_fin] using hz)

theorem node_withoutIncoming_richJet (k : Fin b) (baseline : Z → ℝ) (spacing : ℝ)
    (child childPort parentSelf incoming parentPort : Fin b → Z → ℝ) (z : Z)
    (hb : ContDiff ℝ 2 baseline) (hc : ∀ i,ContDiff ℝ 2 (child i))
    (ho : ∀ i,ContDiff ℝ 2 (childPort i)) (hs : ∀ i,ContDiff ℝ 2 (parentSelf i))
    (hi : ∀ i,ContDiff ℝ 2 (incoming i)) (hp : ∀ i,ContDiff ℝ 2 (parentPort i))
    (hz : ZeroSecondJet (parentPort k) z) (hzChild : ZeroSecondJet (childPort k) z) :
    richJet (node baseline spacing child childPort parentSelf incoming parentPort) z =
      richJet (withoutIncoming k baseline spacing child childPort parentSelf incoming parentPort) z := by
  rw [funext (node_eq_nat baseline spacing child childPort parentSelf incoming parentPort)]
  exact FrontierSecondJet.node_withoutIncoming_richJet_of_zeroSecondJet b k.val baseline spacing
    _ _ _ _ _ z k.isLt hb (extend_contDiff hc) (extend_contDiff ho) (extend_contDiff hs)
    (extend_contDiff hi) (extend_contDiff hp) (by simpa only [extend_fin] using hz)
    (by simpa only [extend_fin] using hzChild)

end GradientHessian.FiniteFrontierBridge
