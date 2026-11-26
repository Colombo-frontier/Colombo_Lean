import GradientHessian.CensoredLeafAgreement
import GradientHessian.SecondJetPullback
import GradientHessian.FiniteFrontierBridge

/-! A literal finite frontier scalar. Every earlier weighted child term is
retained, and the active child is an explicit replaceable scalar. Future
children and their ports are absent. Parent self terms may be replaced by
their disclosed or public versions without changing a local second jet. -/

noncomputable section
namespace GradientHessian.FrontierOracleScalar
open Classical JetLocality SecondJetAlgebra Filter
open scoped BigOperators Topology

variable {b : ℕ} {Z : Type*}

def scalar (k : Fin b) (baseline : Z → ℝ) (spacing : ℝ)
    (child childPort parentSelf incoming parentPort : Fin b → Z → ℝ)
    (active : Z → ℝ) (z : Z) : ℝ :=
  baseline z + (∑ i,if i<k then InnerSelector.weight (fun j => parentPort j z) i *
    (child i z-baseline z-i.val*spacing-incoming i z*childPort i z) else 0) +
    CensoredLeaf.prefixWeight (fun j => parentPort j z) k *
      (active z-baseline z-k.val*spacing) + ∑ i,parentSelf i z

theorem prefix_congr (k : Fin b) {p q : Fin b → ℝ} (he : ∀ i,i<k → p i=q i) :
    CensoredLeaf.prefixWeight p k=CensoredLeaf.prefixWeight q k := by
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i<k
  · simp only [if_pos hi,he i hi]
  · simp only [if_neg hi]

theorem weight_congr (k : Fin b) {p q : Fin b → ℝ} (he : ∀ i,i<k → p i=q i)
    {i : Fin b} (hi : i<k) : InnerSelector.weight p i=InnerSelector.weight q i := by
  change (1-p i)*CensoredLeaf.prefixWeight p i=(1-q i)*CensoredLeaf.prefixWeight q i
  rw [he i hi,prefix_congr i (fun j hj => he j (hj.trans hi))]

theorem scalar_erasure (k : Fin b) (baseline : Z → ℝ) (spacing : ℝ)
    (child childPort parentSelf incoming parentPort : Fin b → Z → ℝ)
    (child' childPort' parentSelf' incoming' parentPort' : Fin b → Z → ℝ)
    (active : Z → ℝ)
    (hc : ∀ i,i<k → child i=child' i)
    (ho : ∀ i,i<k → childPort i=childPort' i)
    (hi : ∀ i,i<k → incoming i=incoming' i)
    (hp : ∀ i,i<k → parentPort i=parentPort' i)
    (hs : parentSelf=parentSelf') :
    scalar k baseline spacing child childPort parentSelf incoming parentPort active=
      scalar k baseline spacing child' childPort' parentSelf' incoming' parentPort' active := by
  funext z
  have hprod := prefix_congr k (fun i h => congrFun (hp i h) z)
  have hsum : (∑ i,if i<k then InnerSelector.weight (fun j => parentPort j z) i *
      (child i z-baseline z-i.val*spacing-incoming i z*childPort i z) else 0)=
    ∑ i,if i<k then InnerSelector.weight (fun j => parentPort' j z) i *
      (child' i z-baseline z-i.val*spacing-incoming' i z*childPort' i z) else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hh : i<k
    · simp only [if_pos hh,hc i hh,ho i hh,hi i hh,
        weight_congr k (fun j hj => congrFun (hp j hj) z) hh]
    · simp only [if_neg hh]
  simp only [scalar,hsum,hprod,hs]

theorem node_eq_scalar (k : Fin b) (baseline : Z → ℝ) (spacing : ℝ)
    (child childPort parentSelf incoming parentPort : Fin b → Z → ℝ) (z : Z)
    (hp : parentPort k z=0) (hc : childPort k z=0) :
    FiniteFrontierBridge.node baseline spacing child childPort parentSelf incoming parentPort z=
      scalar k baseline spacing child childPort parentSelf incoming parentPort (child k) z := by
  have hprod : (∏ i,parentPort i z)=0 := Finset.prod_eq_zero (Finset.mem_univ k) hp
  unfold FiniteFrontierBridge.node scalar
  rw [CensoredLeaf.weighted_prefix _ _ k hp,hprod,hc]
  ring

variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]

omit [NormedSpace ℝ Z] in
theorem node_scalar_near (k : Fin b) (baseline : Z → ℝ) (spacing : ℝ)
    (child childPort parentSelf incoming parentPort : Fin b → Z → ℝ) (z : Z)
    (hp : parentPort k =ᶠ[𝓝 z] fun _ => 0) (hc : childPort k =ᶠ[𝓝 z] fun _ => 0) :
    FiniteFrontierBridge.node baseline spacing child childPort parentSelf incoming parentPort =ᶠ[𝓝 z]
      scalar k baseline spacing child childPort parentSelf incoming parentPort (child k) := by
  filter_upwards [hp,hc] with x hpx hcx
  exact node_eq_scalar k baseline spacing child childPort parentSelf incoming parentPort x hpx hcx

omit [NormedSpace ℝ Z] in
theorem scalar_self_near (k : Fin b) (baseline : Z → ℝ) (spacing : ℝ)
    (child childPort parentSelf incoming parentPort : Fin b → Z → ℝ) (active : Z → ℝ)
    (publicSelf : Fin b → Z → ℝ) (z : Z) (hs : ∀ i,parentSelf i =ᶠ[𝓝 z] publicSelf i) :
    scalar k baseline spacing child childPort parentSelf incoming parentPort active =ᶠ[𝓝 z]
      scalar k baseline spacing child childPort publicSelf incoming parentPort active := by
  filter_upwards [Filter.eventually_all.mpr hs] with x hx
  simp only [scalar,hx]

theorem prefix_contDiff (k : Fin b) (parentPort : Fin b → Z → ℝ)
    (hp : ∀ i,ContDiff ℝ 2 (parentPort i)) :
    ContDiff ℝ 2 (fun z => CensoredLeaf.prefixWeight (fun j => parentPort j z) k) := by
  apply contDiff_prod
  intro i _
  by_cases hi : i<k
  · simpa only [if_pos hi] using hp i
  · simp only [if_neg hi]; exact contDiff_const

theorem scalar_contDiff (k : Fin b) (baseline : Z → ℝ) (spacing : ℝ)
    (child childPort parentSelf incoming parentPort : Fin b → Z → ℝ) (active : Z → ℝ)
    (hb : ContDiff ℝ 2 baseline) (hc : ∀ i,ContDiff ℝ 2 (child i))
    (ho : ∀ i,ContDiff ℝ 2 (childPort i)) (hs : ∀ i,ContDiff ℝ 2 (parentSelf i))
    (hi : ∀ i,ContDiff ℝ 2 (incoming i)) (hp : ∀ i,ContDiff ℝ 2 (parentPort i))
    (ha : ContDiff ℝ 2 active) :
    ContDiff ℝ 2 (scalar k baseline spacing child childPort parentSelf incoming parentPort active) := by
  have hw (i : Fin b) : ContDiff ℝ 2 (fun z => InnerSelector.weight (fun j => parentPort j z) i) :=
    (contDiff_const.sub (hp i)).mul (prefix_contDiff i parentPort hp)
  unfold scalar
  apply ContDiff.add
  · apply ContDiff.add
    · apply hb.add
      apply ContDiff.sum
      intro i _
      by_cases hh : i<k
      · simp only [if_pos hh]
        exact (hw i).mul ((((hc i).sub hb).sub contDiff_const).sub ((hi i).mul (ho i)))
      · simp only [if_neg hh]; exact contDiff_const
    · exact (prefix_contDiff k parentPort hp).mul ((ha.sub hb).sub contDiff_const)
  · exact ContDiff.sum (fun i _ => hs i)

theorem zero_difference_of_richJet_eq {f g : Z → ℝ} {z : Z}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (he : richJet f z=richJet g z) :
    ZeroSecondJet (fun x => f x-g x) z := by
  intro n hn
  have hfn : ContDiffAt ℝ n f z := hf.contDiffAt.of_le (by exact_mod_cast hn)
  have hgn : ContDiffAt ℝ n g z := hg.contDiffAt.of_le (by exact_mod_cast hn)
  simp only [sub_eq_add_neg]
  rw [iteratedFDeriv_add_apply' hfn hgn.neg]
  change iteratedFDeriv ℝ n f z+iteratedFDeriv ℝ n (-g) z=0
  rw [iteratedFDeriv_neg_apply,
    SecondJetPullback.iterated_eq_of_richJet_eq he n hn,add_neg_cancel]

theorem scalar_replace_active_richJet (k : Fin b) (baseline : Z → ℝ) (spacing : ℝ)
    (child childPort parentSelf incoming parentPort : Fin b → Z → ℝ) (active replacement : Z → ℝ)
    (hb : ContDiff ℝ 2 baseline) (hc : ∀ i,ContDiff ℝ 2 (child i))
    (ho : ∀ i,ContDiff ℝ 2 (childPort i)) (hs : ∀ i,ContDiff ℝ 2 (parentSelf i))
    (hi : ∀ i,ContDiff ℝ 2 (incoming i)) (hp : ∀ i,ContDiff ℝ 2 (parentPort i))
    (ha : ContDiff ℝ 2 active) (hr : ContDiff ℝ 2 replacement) (z : Z)
    (he : richJet active z=richJet replacement z) :
    richJet (scalar k baseline spacing child childPort parentSelf incoming parentPort active) z=
      richJet (scalar k baseline spacing child childPort parentSelf incoming parentPort replacement) z := by
  have hf : scalar k baseline spacing child childPort parentSelf incoming parentPort active=
      fun x => scalar k baseline spacing child childPort parentSelf incoming parentPort replacement x+
        CensoredLeaf.prefixWeight (fun j => parentPort j x) k*(active x-replacement x) := by
    funext x
    unfold scalar
    ring
  rw [hf]
  exact SecondJetAlgebra.richJet_remove_gated_term
    (scalar_contDiff k baseline spacing child childPort parentSelf incoming parentPort replacement hb hc ho hs hi hp hr)
    (prefix_contDiff k parentPort hp) (ha.sub hr) (zero_difference_of_richJet_eq ha hr he)

theorem node_censored_richJet (k : Fin b) (baseline : Z → ℝ) (spacing : ℝ)
    (child childPort parentSelf incoming parentPort : Fin b → Z → ℝ)
    (publicSelf : Fin b → Z → ℝ) (replacement : Z → ℝ)
    (hb : ContDiff ℝ 2 baseline) (hc : ∀ i,ContDiff ℝ 2 (child i))
    (ho : ∀ i,ContDiff ℝ 2 (childPort i)) (hs : ∀ i,ContDiff ℝ 2 (publicSelf i))
    (hi : ∀ i,ContDiff ℝ 2 (incoming i)) (hp : ∀ i,ContDiff ℝ 2 (parentPort i))
    (hr : ContDiff ℝ 2 replacement) (z : Z)
    (hparent : parentPort k =ᶠ[𝓝 z] fun _ => 0)
    (hchild : childPort k =ᶠ[𝓝 z] fun _ => 0)
    (hself : ∀ i,parentSelf i =ᶠ[𝓝 z] publicSelf i)
    (hactive : richJet (child k) z=richJet replacement z) :
    richJet (FiniteFrontierBridge.node baseline spacing child childPort parentSelf incoming parentPort) z=
      richJet (scalar k baseline spacing child childPort publicSelf incoming parentPort replacement) z :=
  (richJet_congr_of_eventuallyEq (node_scalar_near k baseline spacing child childPort parentSelf
    incoming parentPort z hparent hchild)).trans
      ((richJet_congr_of_eventuallyEq (scalar_self_near k baseline spacing child childPort parentSelf
        incoming parentPort (child k) publicSelf z hself)).trans
        (scalar_replace_active_richJet k baseline spacing child childPort publicSelf incoming parentPort
          (child k) replacement hb hc ho hs hi hp (hc k) hr z hactive))

end GradientHessian.FrontierOracleScalar
