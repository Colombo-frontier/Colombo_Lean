import Smoothness2601.SineOracle

/-! A finite fresh-sample law as an actual adaptive oracle. This constructor
is used with explicitly proved two-point moments for the boundary instance. -/
noncomputable section
open MeasureTheory ProbabilityTheory Bilevel.PrimitiveGeometry
namespace Smoothness2601.FiniteSampleOracle
variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  {Seed : Type*} [Fintype Seed] [MeasurableSpace Seed] [MeasurableSingletonClass Seed]
  (ν : Measure Seed) [IsProbabilityMeasure ν]
  (sample : Adaptive.Query X Y → Seed → Joint X Y)

def law : Kernel (Adaptive.Query X Y × Unit) (Joint X Y × Unit) :=
  Bilevel.Stateful.KernelMap.dependent (Kernel.const _ ν)
    (fun z => (sample z.1.1 z.2,()))

omit [InnerProductSpace ℝ X] [CompleteSpace X] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [BorelSpace X] [SecondCountableTopology X] [BorelSpace Y] [SecondCountableTopology Y]
  [Fintype Seed] [MeasurableSingletonClass Seed] in
theorem finish_measurable (hs : Measurable (fun z : Adaptive.Query X Y × Seed => sample z.1 z.2)) :
    Measurable (fun z : (Adaptive.Query X Y × Unit) × Seed =>
    (sample z.1.1 z.2,())) :=
  (hs.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).prodMk measurable_const

omit [InnerProductSpace ℝ X] [CompleteSpace X] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [BorelSpace X] [SecondCountableTopology X] [BorelSpace Y] [SecondCountableTopology Y]
  [Fintype Seed] [MeasurableSingletonClass Seed] in
omit [InnerProductSpace ℝ X] [CompleteSpace X] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [BorelSpace X] [SecondCountableTopology X] [BorelSpace Y] [SecondCountableTopology Y]
  [Fintype Seed] [MeasurableSingletonClass Seed] in
theorem law_apply (hs : Measurable (fun z : Adaptive.Query X Y × Seed => sample z.1 z.2))
    (q : Adaptive.Query X Y) (u : Unit) :
    law ν sample (q,u) = ν.map (fun seed => (sample q seed,())) :=
  Bilevel.Stateful.KernelMap.dependent_apply _ _ (finish_measurable sample hs) _

def oracle (hs : Measurable (fun z : Adaptive.Query X Y × Seed => sample z.1 z.2))
    {b : Budgets} (P : Population (X := X) (Y := Y) b)
    (hmean : ∀ q, (∫ seed, sample q seed ∂ν) = Adaptive.trueGradient P q)
    (hvar : ∀ q, (∫ seed, ‖sample q seed-Adaptive.trueGradient P q‖^2 ∂ν) ≤ b.σ^2) :
    Adaptive.Oracle P Unit where
  law := law ν sample
  markov := Bilevel.Stateful.KernelMap.dependent_markov _ _ (finish_measurable sample hs)
  square_integrable := by
    intro q u
    rw [law_apply ν sample hs]
    have hf : Measurable (fun z : Joint X Y × Unit => ‖z.1-Adaptive.trueGradient P q‖^2) := by fun_prop
    exact (integrable_map_measure hf.aestronglyMeasurable (measurable_of_finite _).aemeasurable).mpr
      Integrable.of_finite
  centered := by
    intro q u
    rw [law_apply ν sample hs]
    have hf : Measurable (fun z : Joint X Y × Unit => z.1-Adaptive.trueGradient P q) := by fun_prop
    rw [integral_map (measurable_of_finite _).aemeasurable hf.aestronglyMeasurable,
      integral_sub Integrable.of_finite (integrable_const _),hmean q]
    simp only [integral_const,measureReal_univ_eq_one,one_smul,sub_self]
  variance := by
    intro q u
    rw [law_apply ν sample hs]
    have hf : Measurable (fun z : Joint X Y × Unit => ‖z.1-Adaptive.trueGradient P q‖^2) := by fun_prop
    rw [integral_map (measurable_of_finite _).aemeasurable hf.aestronglyMeasurable]
    exact hvar q

end Smoothness2601.FiniteSampleOracle

namespace Smoothness2601.FreshUpperBernoulli
variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  {b : Budgets} (P : Population (X := X) (Y := Y) b)

def sample (signal : Adaptive.Query X Y → Joint X Y) (p : ℝ)
    (q : Adaptive.Query X Y) (coin : Bool) : Joint X Y :=
  Adaptive.trueGradient P q+
    (if q.1 then 0 else (if coin then p⁻¹ else 0)-1) • signal q

theorem sample_measurable (signal : Adaptive.Query X Y → Joint X Y)
    (hs : Measurable signal) (p : ℝ) :
    Measurable (fun z : Adaptive.Query X Y × Bool => sample P signal p z.1 z.2) := by
  have hc : Measurable (fun z : Adaptive.Query X Y × Bool =>
      if z.1.1 then 0 else (if z.2 then p⁻¹ else (0:ℝ))-1) :=
    (measurable_of_finite (fun z : Bool × Bool =>
      if z.1 then 0 else (if z.2 then p⁻¹ else (0:ℝ))-1)).comp
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  exact ((InnerOracle.trueGradient_measurable P).comp measurable_fst).add
    (hc.smul (hs.comp measurable_fst))

omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y] in
theorem sample_upper (signal : Adaptive.Query X Y → Joint X Y) (p : ℝ)
    (q : X × Y) (coin : Bool) :
    sample P signal p (false,q) coin = BernoulliOracle.response p
      (Adaptive.trueGradient P (false,q)-signal (false,q)) (signal (false,q)) coin := by
  simp only [sample,Bilevel.BernoulliOracle.sample,Bool.false_eq_true,↓reduceIte]
  module

def oracle (signal : Adaptive.Query X Y → Joint X Y) (hs : Measurable signal)
    {B : ℝ} (hB : 0 < B) (hsmall : B ≤ b.σ) (henv : ∀ q, ‖signal q‖ ≤ B) :
    Adaptive.Oracle P Unit :=
  FiniteSampleOracle.oracle
    (BernoulliOracle.law (BernoulliOracle.revealProbability B b.σ)
      (BernoulliOracle.revealProbability_le_one hB.le b.σ_pos hsmall))
    (sample P signal (BernoulliOracle.revealProbability B b.σ)) (sample_measurable P signal hs _) P
    (by
      rintro ⟨flag,q⟩
      cases flag
      · simp only [sample_upper]
        rw [BernoulliOracle.response_mean (BernoulliOracle.revealProbability_pos hB b.σ_pos)]
        exact sub_add_cancel _ _
      · simp only [sample,Bool.true_eq,↓reduceIte,zero_smul,add_zero,
          integral_const,measureReal_univ_eq_one,one_smul])
    (by
      rintro ⟨flag,q⟩
      cases flag
      · simp only [sample_upper]
        have hv := BernoulliOracle.response_variance_le hB b.σ_pos hsmall
          (Adaptive.trueGradient P (false,q)-signal (false,q)) (signal (false,q)) (henv (false,q))
        simpa only [sub_add_cancel] using hv.trans (sub_le_self _ (sq_nonneg B))
      · simp [sample,sq_nonneg])

end Smoothness2601.FreshUpperBernoulli
