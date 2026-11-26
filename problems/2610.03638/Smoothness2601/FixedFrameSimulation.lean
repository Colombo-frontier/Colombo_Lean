import Smoothness2601.SimulationCoupling

/-! Averaging the genuine Haar experiment produces one fixed orthonormal
frame on which the actual randomized algorithm leaves a small coordinate. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace Smoothness2601.PrefixSimulator
open MeasureTheory ProbabilityTheory
open Bilevel EuclideanGaussian ProjectionPosterior PrimitiveGeometry IndependentDraws
open DeferredPrefix
open scoped RealInnerProductSpace ENNReal

variable {d T : ℕ} (A : Adaptive.Algorithm (Space d) ℝ)
variable (reply : Frame d T → Adaptive.Query (Space d) ℝ → Bool → Joint (Space d) ℝ)

def hiddenOutput (coins : ℕ → Bool) (outPoint : Space d → Space d) (δ : ℝ)
    (initial : A.Memory) (N : ℕ) (U : Frame d T) : Prop :=
  ∃ i : Fin T, |⟪outPoint (A.output (realState A reply coins initial U N)),U i⟫| < δ

theorem exists_orthonormal_hidden_output
    (hr : Measurable (fun p : Frame d T × (Adaptive.Query (Space d) ℝ × Bool) => reply p.1 p.2.1 p.2.2))
    (point : Adaptive.Query (Space d) ℝ → Space d) (hp : Measurable point)
    (outPoint : Space d → Space d) (ho : Measurable outPoint)
    {δ R : ℝ} (hδ : 0 < δ) (hR : 0 < R) (hδR : δ ≤ R)
    (hpR : ∀ q, ‖point q‖ ≤ R) (hoR : ∀ x, ‖outPoint x‖ ≤ R)
    (hlocal : ∀ U k q c,
      (∀ i : Fin T, k ≤ i.val → |⟪point q,U i⟫| ≤ δ) →
      reply U q c = reply (truncate U (min T (k+if c then 1 else 0))) q c)
    (n : ℕ) (hd : T+(n+1) ≤ d) (N : ℕ) (hT : 1 ≤ T)
    (hlog : Real.log (16*((N+1 : ℕ) : ℝ)*T) ≤ (n : ℝ)*δ^2/(8*R^2))
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hbudget : (N : ℝ)*q ≤ T/8)
    (ν : Measure A.Memory) [IsProbabilityMeasure ν] :
    ∃ U : Frame d T, Orthonormal ℝ U ∧
      (1/2 : ℝ≥0∞) < ∫⁻ m, ∫⁻ c,
        if hiddenOutput A reply (coinSequence N c) outPoint δ m N U then (1:ℝ≥0∞) else 0
        ∂law (Bilevel.BernoulliOracle.law q hq1) N ∂ν := by
  let μ := HaarFrame.frameLaw d T (by omega)
  let κ := law (Bilevel.BernoulliOracle.law q hq1) N
  let good : Set (Draws Bool N × (A.Memory × Frame d T)) :=
    ({p | experimentBad A reply point outPoint δ N p} ∪
      {p | experimentSaturated (T := T) A N p})ᶜ
  have hg : MeasurableSet good :=
    ((experimentBad_measurable A reply hr point hp outPoint ho δ N).union
      (experimentSaturated_measurable A N)).compl
  have hprob : ENNReal.ofReal (3/4 : ℝ) ≤ (κ.prod (ν.prod μ)) good := by
    have hp' := ENNReal.ofReal_le_ofReal (experiment_good_probability A reply hr point hp outPoint ho
      hδ hR hδR hpR hoR n hd N hT hlog q hq0 hq1 hbudget ν)
    simpa only [Measure.real,ENNReal.ofReal_toReal (measure_ne_top _ _)] using hp'
  have hi : (1/2 : ℝ≥0∞) < ∫⁻ p, good.indicator (fun _ => (1:ℝ≥0∞)) p ∂κ.prod (ν.prod μ) := by
    rw [lintegral_indicator_const hg,one_mul]
    have hhalf : (1/2 : ℝ≥0∞) = ENNReal.ofReal (1/2 : ℝ) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2)]
      norm_num
    rw [hhalf]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0:ℝ) < 3/4)).mpr (by norm_num) |>.trans_le hprob
  obtain ⟨U,hU,hlarge⟩ := LowerRisk.fixed_frame_three κ ν μ (Orthonormal ℝ)
    (ProjectionConcentration.haar_orthonormal_ae d T (by omega))
    (good.indicator (fun _ => (1:ℝ≥0∞))) (measurable_const.indicator hg) (1/2) hi
  refine ⟨U,hU,hlarge.trans_le ?_⟩
  apply lintegral_mono
  intro m
  apply lintegral_mono
  intro c
  dsimp only
  by_cases hc : (c,(m,U)) ∈ good
  · rw [Set.indicator_of_mem hc]
    have hn : ¬ (experimentBad A reply point outPoint δ N (c,(m,U)) ∨
        experimentSaturated (T := T) A N (c,(m,U))) := hc
    have hb : ¬ experimentBad A reply point outPoint δ N (c,(m,U)) := fun h => hn (Or.inl h)
    have hs : ¬ experimentSaturated (T := T) A N (c,(m,U)) := fun h => hn (Or.inr h)
    have hh := real_output_hidden A reply point outPoint δ hlocal (coinSequence N c) m U N hb hs
    have hh' : hiddenOutput A reply (coinSequence N c) outPoint δ m N U := hh
    rw [if_pos hh']
  · rw [Set.indicator_of_not_mem hc]
    exact zero_le _

end Smoothness2601.PrefixSimulator
