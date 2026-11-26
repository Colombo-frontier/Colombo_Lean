import NCConcave16991.MixedHaarFrameProbability
import NCConcave16991.MixedHaarCanonicalCoordinates

/-! # Fresh Gaussian normalization is measurable and almost surely legal in every frame -/

noncomputable section

open Set MeasureTheory ProbabilityTheory

namespace NCConcave16991.MixedHaar

set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 100000

attribute [local irreducible] frameTail prefixSpan tailIsometry Haar.orthogonalLinearIsometryEquiv

variable {k : ℕ}

def frameGaussianGood (s : FrameState k) (g : Space k) : Prop :=
  s.1.val = k ∨ frameTail s.1 s.2.1 g ≠ 0

theorem frameTail_norm_measurable :
    Measurable (fun p : FrameState k × Space k ↦ ‖frameTail p.1.1 p.1.2.1 p.2‖) := by
  apply measurable_finite_indexed (fun p : FrameState k × Space k ↦ p.1.1)
    (measurable_fst.comp measurable_fst)
    (fun r p ↦ ‖frameTail r p.1.2.1 p.2‖)
  intro r
  exact ((frameTail_continuous r).measurable.comp
    ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd)).norm

theorem frameGaussianGood_measurableSet :
    MeasurableSet {p : FrameState k × Space k | frameGaussianGood p.1 p.2} := by
  have hr : Measurable (fun p : FrameState k × Space k ↦ p.1.1.val) :=
    (measurable_of_countable (fun r : Fin (k + 1) ↦ r.val)).comp (measurable_fst.comp measurable_fst)
  have hfull : MeasurableSet {p : FrameState k × Space k | p.1.1.val = k} :=
    measurableSet_eq_fun hr measurable_const
  have hzero : MeasurableSet {p : FrameState k × Space k | ‖frameTail p.1.1 p.1.2.1 p.2‖ = 0} :=
    measurableSet_eq_fun frameTail_norm_measurable measurable_const
  convert hfull.union hzero.compl using 1
  ext p
  simp only [frameGaussianGood,mem_union,mem_setOf_eq,mem_compl_iff,norm_ne_zero_iff]

theorem frameGaussianGood_fixed_measurableSet (s : FrameState k) :
    MeasurableSet {g : Space k | frameGaussianGood s g} :=
  frameGaussianGood_measurableSet.preimage (measurable_const.prodMk measurable_id)

theorem frameGaussianGood_ae (s : FrameState k) :
    ∀ᵐ g ∂stdGaussian (Space k), frameGaussianGood s g := by
  by_cases hfull : s.1.val = k
  · exact Filter.Eventually.of_forall (fun _ ↦ Or.inl hfull)
  · have hr : s.1.val < k := by have h := s.1.isLt; omega
    filter_upwards [frameTail_ne_zero_ae s.1 s.2.1 (firstTailVector s.1 hr) (firstTailVector_unit s.1 hr)] with g hg
    exact Or.inr hg

end NCConcave16991.MixedHaar
