import GradientHessian.FrontierTruncation
import GradientHessian.SecondJetAlgebra

/-! Frontier truncation at flat endpoints. The literal difference between a
node and its truncated frontier factors through the active parent port.
Its zero second jet suffices; a neighborhood plateau is unnecessary. -/

noncomputable section
namespace GradientHessian.FrontierSecondJet

open FrontierTruncation SecondJetAlgebra
open scoped BigOperators

def tailCoefficient (b k : ℕ) (port payload : ℕ → ℝ) : ℝ :=
  (∑ i ∈ Finset.range b \ Finset.range (k+1),
    (1-port i)*(∏ j ∈ (Finset.range i).erase k, port j)*payload i) -
    Selectors.prefixProduct port k*payload k

theorem weighted_factor (b k : ℕ) (hk : k < b) (port payload : ℕ → ℝ) :
    (∑ i ∈ Finset.range b,Selectors.weight port i*payload i) =
      (∑ i ∈ Finset.range k,Selectors.weight port i*payload i) +
        Selectors.prefixProduct port k*payload k + port k*tailCoefficient b k port payload := by
  have hs := Finset.sum_sdiff (f := fun i => Selectors.weight port i*payload i)
    (Finset.range_mono (show k+1 ≤ b by omega))
  rw [Finset.sum_range_succ] at hs
  have ht : (∑ i ∈ Finset.range b \ Finset.range (k+1),Selectors.weight port i*payload i) =
      port k * ∑ i ∈ Finset.range b \ Finset.range (k+1),
        (1-port i)*(∏ j ∈ (Finset.range i).erase k,port j)*payload i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hki : k < i := by
      have hh := (Finset.mem_sdiff.mp hi).2
      simp only [Finset.mem_range,not_lt] at hh
      omega
    have hp := Finset.mul_prod_erase (Finset.range i) port (Finset.mem_range.mpr hki)
    unfold Selectors.weight Selectors.prefixProduct
    rw [← hp]
    ring
  rw [← hs,ht]
  unfold tailCoefficient Selectors.weight
  ring

variable {Z : Type*}

def remainderScalar (b k : ℕ) (baseline : Z → ℝ) (spacing : ℝ)
    (child childPort incoming parentPort : ℕ → Z → ℝ) (z : Z) : ℝ :=
  tailCoefficient b k (fun j => parentPort j z)
    (fun i => child i z-baseline z-i*spacing-incoming i z*childPort i z) -
    b*spacing*(∏ j ∈ (Finset.range b).erase k,parentPort j z)

theorem node_frontier_factor (b k : ℕ) (baseline : Z → ℝ) (spacing : ℝ)
    (child childPort parentSelf incoming parentPort : ℕ → Z → ℝ) (z : Z) (hk : k < b) :
    Hierarchy.nodeScalar b baseline spacing child childPort parentSelf incoming parentPort z =
      frontierScalar b k baseline spacing child childPort parentSelf incoming parentPort z +
        remainderScalar b k baseline spacing child childPort incoming parentPort z*parentPort k z := by
  have hp := Finset.mul_prod_erase (Finset.range b) (fun j => parentPort j z)
    (Finset.mem_range.mpr hk)
  unfold Hierarchy.nodeScalar frontierScalar remainderScalar
  rw [weighted_factor b k hk]
  change _ - _*Selectors.prefixProduct (fun j => parentPort j z) b + _ = _
  rw [show Selectors.prefixProduct (fun j => parentPort j z) b =
    parentPort k z*(∏ j ∈ (Finset.range b).erase k,parentPort j z) from hp.symm]
  ring

variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- The pointwise zero-jet frontier theorem. The regularity premises are on
the literal component functions; no simulated reply or support is assumed. -/
theorem node_frontier_richJet_of_zeroSecondJet (b k : ℕ) (baseline : Z → ℝ) (spacing : ℝ)
    (child childPort parentSelf incoming parentPort : ℕ → Z → ℝ) (z : Z) (hk : k < b)
    (hb : ContDiff ℝ 2 baseline) (hc : ∀ i,ContDiff ℝ 2 (child i))
    (ho : ∀ i,ContDiff ℝ 2 (childPort i)) (hs : ∀ i,ContDiff ℝ 2 (parentSelf i))
    (hi : ∀ i,ContDiff ℝ 2 (incoming i)) (hp : ∀ i,ContDiff ℝ 2 (parentPort i))
    (hz : ZeroSecondJet (parentPort k) z) :
    JetLocality.richJet
      (Hierarchy.nodeScalar b baseline spacing child childPort parentSelf incoming parentPort) z =
      JetLocality.richJet
        (frontierScalar b k baseline spacing child childPort parentSelf incoming parentPort) z := by
  have hprod (t : Finset ℕ) : ContDiff ℝ 2 (fun x => ∏ j ∈ t,parentPort j x) :=
    contDiff_prod (fun j _ => hp j)
  have hpay (i : ℕ) : ContDiff ℝ 2
      (fun x => child i x-baseline x-i*spacing-incoming i x*childPort i x) := by fun_prop
  have hw (i : ℕ) : ContDiff ℝ 2 (fun x => Selectors.weight (fun j => parentPort j x) i) :=
    (contDiff_const.sub (hp i)).mul (hprod (Finset.range i))
  have he : Hierarchy.nodeScalar b baseline spacing child childPort parentSelf incoming parentPort =
      fun x => frontierScalar b k baseline spacing child childPort parentSelf incoming parentPort x +
        remainderScalar b k baseline spacing child childPort incoming parentPort x*parentPort k x :=
    funext (fun x => node_frontier_factor b k baseline spacing child childPort parentSelf incoming parentPort x hk)
  rw [he]
  apply richJet_remove_gated_term _ _ (hp k) hz
  · exact ((hb.add (ContDiff.sum (fun i _ => (hw i).mul (hpay i)))).add
      ((hprod (Finset.range k)).mul (hpay k))).add (ContDiff.sum (fun i _ => hs i))
  · exact ((ContDiff.sum (fun i _ =>
      (((contDiff_const.sub (hp i)).mul (hprod ((Finset.range i).erase k))).mul (hpay i)))).sub
      ((hprod (Finset.range k)).mul (hpay k))).sub
      (contDiff_const.mul (hprod ((Finset.range b).erase k)))

theorem node_withoutIncoming_richJet_of_zeroSecondJet (b k : ℕ) (baseline : Z → ℝ) (spacing : ℝ)
    (child childPort parentSelf incoming parentPort : ℕ → Z → ℝ) (z : Z) (hk : k < b)
    (hb : ContDiff ℝ 2 baseline) (hc : ∀ i,ContDiff ℝ 2 (child i))
    (ho : ∀ i,ContDiff ℝ 2 (childPort i)) (hs : ∀ i,ContDiff ℝ 2 (parentSelf i))
    (hi : ∀ i,ContDiff ℝ 2 (incoming i)) (hp : ∀ i,ContDiff ℝ 2 (parentPort i))
    (hparent : ZeroSecondJet (parentPort k) z) (hchild : ZeroSecondJet (childPort k) z) :
    JetLocality.richJet
      (Hierarchy.nodeScalar b baseline spacing child childPort parentSelf incoming parentPort) z =
      JetLocality.richJet
        (frontierWithoutIncoming b k baseline spacing child childPort parentSelf incoming parentPort) z := by
  have hprod (t : Finset ℕ) : ContDiff ℝ 2 (fun x => ∏ j ∈ t,parentPort j x) :=
    contDiff_prod (fun j _ => hp j)
  have hpay (i : ℕ) : ContDiff ℝ 2
      (fun x => child i x-baseline x-i*spacing-incoming i x*childPort i x) := by fun_prop
  have hw (i : ℕ) : ContDiff ℝ 2 (fun x => Selectors.weight (fun j => parentPort j x) i) :=
    (contDiff_const.sub (hp i)).mul (hprod (Finset.range i))
  rw [node_frontier_richJet_of_zeroSecondJet b k baseline spacing child childPort parentSelf incoming parentPort
    z hk hb hc ho hs hi hp hparent]
  have he : frontierScalar b k baseline spacing child childPort parentSelf incoming parentPort =
      fun x => frontierWithoutIncoming b k baseline spacing child childPort parentSelf incoming parentPort x -
        (Selectors.prefixProduct (fun j => parentPort j x) k*incoming k x)*childPort k x := by
    funext x
    unfold frontierScalar frontierWithoutIncoming
    ring
  rw [he]
  apply richJet_remove_sub_gated_term _ _ (ho k) hchild
  · exact ((hb.add (ContDiff.sum (fun i _ => (hw i).mul (hpay i)))).add
      ((hprod (Finset.range k)).mul (((hc k).sub hb).sub contDiff_const))).add
      (ContDiff.sum (fun i _ => hs i))
  · exact (hprod (Finset.range k)).mul (hi k)

end GradientHessian.FrontierSecondJet
