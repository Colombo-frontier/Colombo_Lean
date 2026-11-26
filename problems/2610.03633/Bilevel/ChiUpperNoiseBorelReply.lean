import Bilevel.ChiVirtualUpperReply
import Bilevel.ChiUpperNoiseJointOracle

/-! A direct upper-noise reply uses the inactive scalar from the old store,
the active scalar from the success-updated store, and the public lower
gradient. The same input order is used by the actual hierarchy execution. -/
noncomputable section
open MeasureTheory
open scoped Topology
namespace Bilevel.ChiUpperNoise
variable {Data Q : Type*}
  [TopologicalSpace Data] [MeasurableSpace Data] [BorelSpace Data]
  [SecondCountableTopology Data]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q]
  [FiniteDimensional ℝ Q] [MeasurableSpace Q] [BorelSpace Q]
  [SecondCountableTopology Q]

def twoStorePair (f f₀ : Data → Q → ℝ) (g : Q → ℝ) (π : ℝ)
    (q : Q) (old new : Data) (coin : Bool) : Q × Q :=
  (BernoulliOracle.sample π (gradient (f₀ old) q)
    (gradient (f new) q-gradient (f₀ old) q) coin,gradient g q)

omit [SecondCountableTopology Data] in
theorem twoStorePair_measurable (f f₀ : Data → Q → ℝ) (g : Q → ℝ) (π : ℝ)
    (hf : Continuous (Function.uncurry f)) (hf₀ : Continuous (Function.uncurry f₀))
    (hg : Continuous g) :
    Measurable (fun p : Q × (Data × (Data × Bool)) =>
      twoStorePair f f₀ g π p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hold : Measurable (fun p : Q × (Data × (Data × Bool)) => (p.2.1,p.1)) :=
    measurable_snd.fst.prodMk measurable_fst
  have hnew : Measurable (fun p : Q × (Data × (Data × Bool)) => (p.2.2.1,p.1)) :=
    measurable_snd.snd.fst.prodMk measurable_fst
  have hzero := (ParametricGradient.gradient_measurable f₀ hf₀).comp hold
  have hone := (ParametricGradient.gradient_measurable f hf).comp hnew
  have hcoin : Measurable (fun p : Q × (Data × (Data × Bool)) =>
      if p.2.2.2 then π⁻¹ else (0:ℝ)) :=
    (measurable_of_finite (fun b : Bool => if b then π⁻¹ else (0:ℝ))).comp measurable_snd.snd.snd
  have hgrad := ParametricGradient.gradient_measurable (fun _ : Unit => g)
    (hg.comp continuous_snd)
  have hlower := hgrad.comp (measurable_const.prodMk measurable_fst :
    Measurable (fun p : Q × (Data × (Data × Bool)) => ((),p.1)))
  exact (hzero.add (hcoin.smul (hone.sub hzero))).prodMk hlower

omit [TopologicalSpace Data] [MeasurableSpace Data] [BorelSpace Data] [SecondCountableTopology Data]
  [FiniteDimensional ℝ Q] [MeasurableSpace Q] [BorelSpace Q] [SecondCountableTopology Q] in
theorem twoStorePair_eq_original (f f₀ : Data → Q → ℝ) (g a a₀ : Q → ℝ)
    (π : ℝ) (q : Q) (old new : Data) (coin : Bool)
    (hzero : f₀ old =ᶠ[𝓝 q] a₀) (hone : coin=true → f new =ᶠ[𝓝 q] a) :
    twoStorePair f f₀ g π q old new coin=
      (ChiConservative.sampleGradient a a₀ π coin q,gradient g q) := by
  have hz := hzero.gradient_eq
  cases coin with
  | false => simp only [twoStorePair,ChiConservative.sampleGradient,BernoulliOracle.sample,
      Bool.false_eq_true,if_false,zero_smul,add_zero,hz]
  | true => simp only [twoStorePair,ChiConservative.sampleGradient,hz,(hone rfl).gradient_eq]

end Bilevel.ChiUpperNoise
