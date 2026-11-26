import Smoothness2601.BernoulliOracle
import Smoothness2601.InnerOracle
import Smoothness2601.SineAdmissible

/-! The actual fresh two-loss oracle, with exact full f-gradients, in the
unrestricted adaptive execution model. -/
noncomputable section
open MeasureTheory ProbabilityTheory Bilevel.PrimitiveGeometry
namespace Smoothness2601.FreshBernoulli
variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  {b : Budgets} (P : Population (X := X) (Y := Y) b)

def sample (signal : Adaptive.Query X Y → Joint X Y) (p : ℝ)
    (q : Adaptive.Query X Y) (coin : Bool) : Joint X Y :=
  Adaptive.trueGradient P q+
    (if q.1 then (if coin then p⁻¹ else 0)-1 else 0) • signal q

theorem sample_measurable (signal : Adaptive.Query X Y → Joint X Y)
    (hs : Measurable signal) (p : ℝ) :
    Measurable (fun z : Adaptive.Query X Y × Bool => sample P signal p z.1 z.2) := by
  have hc : Measurable (fun z : Adaptive.Query X Y × Bool =>
      if z.1.1 then (if z.2 then p⁻¹ else (0:ℝ))-1 else 0) :=
    (measurable_of_finite (fun z : Bool × Bool =>
      if z.1 then (if z.2 then p⁻¹ else (0:ℝ))-1 else 0)).comp
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  exact ((InnerOracle.trueGradient_measurable P).comp measurable_fst).add
    (hc.smul (hs.comp measurable_fst))

omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y] in
theorem sample_lower (signal : Adaptive.Query X Y → Joint X Y) (p : ℝ)
    (q : X × Y) (coin : Bool) :
    sample P signal p (true,q) coin = BernoulliOracle.response p
      (Adaptive.trueGradient P (true,q)-signal (true,q)) (signal (true,q)) coin := by
  simp only [sample,Bilevel.BernoulliOracle.sample,Bool.true_eq,↓reduceIte]
  module

omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y] in
theorem sample_upper (signal : Adaptive.Query X Y → Joint X Y) (p : ℝ)
    (q : X × Y) (coin : Bool) :
    sample P signal p (false,q) coin = P.grad_f (pack q.1 q.2) := by
  simp [sample,Adaptive.trueGradient]

def law (signal : Adaptive.Query X Y → Joint X Y) (p : ℝ) (hp : p ≤ 1) :
    Kernel (Adaptive.Query X Y × Unit) (Joint X Y × Unit) :=
  Bilevel.Stateful.KernelMap.dependent
    (Kernel.const _ (BernoulliOracle.law p hp))
    (fun z => (sample P signal p z.1.1 z.2,()))

theorem finish_measurable (signal : Adaptive.Query X Y → Joint X Y)
    (hs : Measurable signal) (p : ℝ) :
    Measurable (fun z : (Adaptive.Query X Y × Unit) × Bool =>
      (sample P signal p z.1.1 z.2,())) :=
  ((sample_measurable P signal hs p).comp
    ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).prodMk measurable_const

theorem law_apply (signal : Adaptive.Query X Y → Joint X Y)
    (hs : Measurable signal) (p : ℝ) (hp : p ≤ 1) (q : Adaptive.Query X Y) (u : Unit) :
    law P signal p hp (q,u) =
      (BernoulliOracle.law p hp).map (fun coin => (sample P signal p q coin,())) :=
  Bilevel.Stateful.KernelMap.dependent_apply _ _ (finish_measurable P signal hs p) _

def oracle (signal : Adaptive.Query X Y → Joint X Y) (hs : Measurable signal)
    {B : ℝ} (hB : 0 < B) (hsmall : B ≤ b.σ) (henv : ∀ q, ‖signal q‖ ≤ B) :
    Adaptive.Oracle P Unit where
  law := law P signal (BernoulliOracle.revealProbability B b.σ)
    (BernoulliOracle.revealProbability_le_one hB.le b.σ_pos hsmall)
  markov := Bilevel.Stateful.KernelMap.dependent_markov _ _
    (finish_measurable P signal hs _)
  square_integrable := by
    intro q u
    rw [law_apply P signal hs]
    have hf : Measurable (fun z : Joint X Y × Unit => ‖z.1-Adaptive.trueGradient P q‖^2) := by fun_prop
    exact (integrable_map_measure hf.aestronglyMeasurable (measurable_of_finite _).aemeasurable).mpr
      Integrable.of_finite
  centered := by
    intro q u
    rw [law_apply P signal hs]
    have hf : Measurable (fun z : Joint X Y × Unit => z.1-Adaptive.trueGradient P q) := by fun_prop
    rw [integral_map (measurable_of_finite _).aemeasurable hf.aestronglyMeasurable]
    rcases q with ⟨flag,q⟩
    cases flag
    · simp [sample,Adaptive.trueGradient]
    · simp only [sample_lower]
      rw [integral_sub Integrable.of_finite (integrable_const _),
        BernoulliOracle.response_mean (BernoulliOracle.revealProbability_pos hB b.σ_pos)]
      simp only [integral_const,measureReal_univ_eq_one,one_smul,sub_add_cancel,sub_self]
  variance := by
    intro q u
    rw [law_apply P signal hs]
    have hf : Measurable (fun z : Joint X Y × Unit => ‖z.1-Adaptive.trueGradient P q‖^2) := by fun_prop
    rw [integral_map (measurable_of_finite _).aemeasurable hf.aestronglyMeasurable]
    rcases q with ⟨flag,q⟩
    cases flag
    · simp [sample,Adaptive.trueGradient,sq_nonneg]
    · simp only [sample_lower]
      have hv := BernoulliOracle.response_variance_le hB b.σ_pos hsmall
        (Adaptive.trueGradient P (true,q)-signal (true,q)) (signal (true,q)) (henv (true,q))
      simpa only [sub_add_cancel] using hv.trans (sub_le_self _ (sq_nonneg B))

end Smoothness2601.FreshBernoulli

namespace Smoothness2601.SineGeometry.Profiles
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  (F : Profiles X) {b : Budgets} (S : F.Calibration b)

omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] in
theorem signal_continuous : Continuous (F.signal S.m S.a S.h) := by
  have hn : 0 ≤ F.signalLipschitz S.m S.a S.h := by
    unfold signalLipschitz
    have := S.m_nonneg
    have := S.a_nonneg
    have := S.h_pos
    have := F.C₀_nonneg
    have := F.C₁_nonneg
    have := F.C₂_nonneg
    positivity
  exact (LipschitzWith.of_dist_le_mul (K := ⟨F.signalLipschitz S.m S.a S.h,hn⟩)
    (fun z w => by simpa only [dist_eq_norm,NNReal.coe_mk] using
      F.signal_difference S.m_nonneg S.a_nonneg S.h_pos z w)).continuous

def oracle {B : ℝ} (hB : 0 < B) (hsmall : B ≤ b.σ)
    (henv : S.m*S.a*S.h*F.C₁+S.m*S.a*F.C₀ ≤ B) : Adaptive.Oracle (F.population S) Unit :=
  FreshBernoulli.oracle (F.population S)
    (fun q => F.signal S.m S.a S.h (pack q.2.1 q.2.2))
    ((F.signal_continuous S).measurable.comp
      ((packLinear (X := X) (Y := ℝ)).continuous.measurable.comp measurable_snd))
    hB hsmall (fun q => (F.signal_norm S.m_nonneg S.a_nonneg S.h_pos.le (pack q.2.1 q.2.2)).trans henv)

end Smoothness2601.SineGeometry.Profiles
