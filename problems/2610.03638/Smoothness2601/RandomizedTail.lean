import Smoothness2601.AdaptiveTail
import Smoothness2601.FiniteCoins
import Smoothness2601.LowerRisk

/-! The complete product experiment: private initial memory, independent
Bernoulli coins, and an independent Haar frame. -/
noncomputable section
namespace Smoothness2601.PrefixSimulator
open MeasureTheory ProbabilityTheory
open Bilevel EuclideanGaussian ProjectionPosterior PrimitiveGeometry IndependentDraws
open DeferredPrefix
open scoped BigOperators RealInnerProductSpace ENNReal

theorem measurableSet_countable_slices {C X : Type*} [Countable C] [MeasurableSpace C]
    [MeasurableSingletonClass C] [MeasurableSpace X] (s : C → Set X)
    (hs : ∀ c, MeasurableSet (s c)) : MeasurableSet {p : C × X | p.2 ∈ s p.1} := by
  have he : {p : C × X | p.2 ∈ s p.1} = ⋃ c : C, ({c} ×ˢ s c) := by
    ext p
    simp
  rw [he]
  exact MeasurableSet.iUnion fun c => (measurableSet_singleton c).prod (hs c)

variable {d T : ℕ} (A : Adaptive.Algorithm (Space d) ℝ)
variable (reply : Frame d T → Adaptive.Query (Space d) ℝ → Bool → Joint (Space d) ℝ)

def experimentBad (point : Adaptive.Query (Space d) ℝ → Space d) (outPoint : Space d → Space d)
    (δ : ℝ) (N : ℕ) (p : Draws Bool N × (A.Memory × Frame d T)) : Prop :=
  queryBad A reply (coinSequence N p.1) point δ p.2.1 N p.2.2 ∨
    outputBad A reply (coinSequence N p.1) outPoint δ p.2.1 N p.2.2

def experimentSaturated (N : ℕ) (p : Draws Bool N × (A.Memory × Frame d T)) : Prop :=
  T ≤ prefixCount T (coinSequence N p.1) N

theorem experimentBad_measurable
    (hr : Measurable (fun p : Frame d T × (Adaptive.Query (Space d) ℝ × Bool) => reply p.1 p.2.1 p.2.2))
    (point : Adaptive.Query (Space d) ℝ → Space d) (hp : Measurable point)
    (outPoint : Space d → Space d) (ho : Measurable outPoint) (δ : ℝ) (N : ℕ) :
    MeasurableSet {p | experimentBad A reply point outPoint δ N p} := by
  apply measurableSet_countable_slices (fun c => {p : A.Memory × Frame d T |
    queryBad A reply (coinSequence N c) point δ p.1 N p.2 ∨
      outputBad A reply (coinSequence N c) outPoint δ p.1 N p.2})
  intro c
  exact (queryBad_joint_measurable A reply (coinSequence N c) hr point hp δ N).union
    (outputBad_joint_measurable A reply (coinSequence N c) hr outPoint ho δ N)

theorem experimentSaturated_measurable (N : ℕ) :
    MeasurableSet {p | experimentSaturated (T := T) A N p} := by
  apply measurableSet_countable_slices (fun c => {p : A.Memory × Frame d T |
    T ≤ prefixCount T (coinSequence N c) N})
  intro c
  by_cases h : T ≤ prefixCount T (coinSequence N c) N <;> simp [experimentSaturated,h]

theorem experiment_failure_small
    (hr : Measurable (fun p : Frame d T × (Adaptive.Query (Space d) ℝ × Bool) => reply p.1 p.2.1 p.2.2))
    (point : Adaptive.Query (Space d) ℝ → Space d) (hp : Measurable point)
    (outPoint : Space d → Space d) (ho : Measurable outPoint)
    {δ R : ℝ} (hδ : 0 < δ) (hR : 0 < R) (hδR : δ ≤ R)
    (hpR : ∀ q, ‖point q‖ ≤ R) (hoR : ∀ x, ‖outPoint x‖ ≤ R)
    (n : ℕ) (hd : T+(n+1) ≤ d) (N : ℕ) (hT : 1 ≤ T)
    (hlog : Real.log (16*((N+1 : ℕ) : ℝ)*T) ≤ (n : ℝ)*δ^2/(8*R^2))
    (ν : Measure A.Memory) [IsProbabilityMeasure ν]
    (coinLaw : Measure (Draws Bool N)) [IsProbabilityMeasure coinLaw] :
    (coinLaw.prod (ν.prod (HaarFrame.frameLaw d T (by omega))))
      {p | experimentBad A reply point outPoint δ N p} ≤ ENNReal.ofReal (1/8 : ℝ) := by
  rw [Measure.prod_apply (experimentBad_measurable A reply hr point hp outPoint ho δ N)]
  calc
    _ ≤ ∫⁻ _c, ENNReal.ofReal (1/8 : ℝ) ∂coinLaw := by
      apply lintegral_mono
      intro c
      exact haar_randomized_failure_small A reply (coinSequence N c) hr point hp outPoint ho
        hδ hR hδR hpR hoR n hd N hT hlog ν
    _ = _ := by simp

theorem experiment_saturation_probability (N : ℕ) (hT : 0 < T) (q : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hbudget : (N : ℝ)*q ≤ T/8)
    (ν : Measure A.Memory) [IsProbabilityMeasure ν]
    (μ : Measure (Frame d T)) [IsProbabilityMeasure μ] :
    ((law (Bilevel.BernoulliOracle.law q hq1) N).prod (ν.prod μ)).real
      {p | experimentSaturated (T := T) A N p} ≤ 1/8 := by
  have he : {p | experimentSaturated (T := T) A N p} =
      {c : Draws Bool N | T ≤ prefixCount T (coinSequence N c) N} ×ˢ (Set.univ : Set (A.Memory × Frame d T)) := by
    ext p
    simp [experimentSaturated]
  rw [he,measureReal_prod_prod,measureReal_univ_eq_one,mul_one]
  exact saturation_probability_eighth N T hT q hq0 hq1 hbudget

theorem experiment_good_probability
    (hr : Measurable (fun p : Frame d T × (Adaptive.Query (Space d) ℝ × Bool) => reply p.1 p.2.1 p.2.2))
    (point : Adaptive.Query (Space d) ℝ → Space d) (hp : Measurable point)
    (outPoint : Space d → Space d) (ho : Measurable outPoint)
    {δ R : ℝ} (hδ : 0 < δ) (hR : 0 < R) (hδR : δ ≤ R)
    (hpR : ∀ q, ‖point q‖ ≤ R) (hoR : ∀ x, ‖outPoint x‖ ≤ R)
    (n : ℕ) (hd : T+(n+1) ≤ d) (N : ℕ) (hT : 1 ≤ T)
    (hlog : Real.log (16*((N+1 : ℕ) : ℝ)*T) ≤ (n : ℝ)*δ^2/(8*R^2))
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hbudget : (N : ℝ)*q ≤ T/8)
    (ν : Measure A.Memory) [IsProbabilityMeasure ν] :
    (3/4 : ℝ) ≤ ((law (Bilevel.BernoulliOracle.law q hq1) N).prod
      (ν.prod (HaarFrame.frameLaw d T (by omega)))).real
      ({p | experimentBad A reply point outPoint δ N p} ∪
        {p | experimentSaturated (T := T) A N p})ᶜ := by
  apply LowerRisk.good_probability _ _ _
    (experimentBad_measurable A reply hr point hp outPoint ho δ N)
    (experimentSaturated_measurable A N)
  · have hb := experiment_failure_small A reply hr point hp outPoint ho hδ hR hδR hpR hoR
      n hd N hT hlog ν (law (Bilevel.BernoulliOracle.law q hq1) N)
    have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
    simpa only [Measure.real,ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 1/8)] using ht
  · exact experiment_saturation_probability A N (by omega) q hq0 hq1 hbudget ν _

end Smoothness2601.PrefixSimulator
