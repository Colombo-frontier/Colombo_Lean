import Bilevel.BernoulliOracle
import Bilevel.FreshOracle
import Bilevel.IndependentStream

/-! At zero variance the actual Bernoulli seed law is a point mass. The
exceptional null set is common to all queries, hence also to adaptive queries. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory
namespace Bilevel.BernoulliOracle

theorem probability_zero {B : ℝ} (hB : 0<B) : probability B 0=1 := by
  simp [probability, pow_ne_zero 2 hB.ne']

theorem law_one (h : (1:ℝ)≤1) : law 1 h=Measure.dirac true := by
  have he : PMF.bernoulli (ENNReal.ofReal (1:ℝ)) (ENNReal.ofReal_le_one.mpr h)=PMF.pure true := by
    ext b
    cases b <;> simp [PMF.bernoulli_apply, PMF.pure_apply]
  rw [law,he,PMF.toMeasure_pure]

theorem zero_law {B : ℝ} (hB : 0<B) :
    law (probability B 0) (probability_le_one hB)=Measure.dirac true := by
  simp only [probability_zero hB]
  exact law_one _

theorem stream_one : ∀ᵐ z ∂IndependentStream.law (law 1 (by rfl)), ∀ i,z i=true := by
  apply ae_all_iff.mpr
  intro i
  have hh : ∀ᵐ b ∂law 1 (by rfl),b=true := by
    rw [law_one]
    simp
  exact (IndependentStream.coordinate_preserves (law 1 (by rfl)) i).quasiMeasurePreserving.ae hh

variable {Query E : Type*} [MeasurableSpace Query]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem oracle_true {B σ : ℝ} (hB : 0<B)
    (O : FreshOracle.Oracle (Query:=Query) (E:=E)
      (law (probability B 0) (probability_le_one hB)) σ) (q : Query) :
    O.sample q true=O.truth q := by
  have hh := O.sample_mean q
  simpa only [zero_law hB,integral_dirac] using hh

theorem oracle_uniform_exact {B σ : ℝ} (hB : 0<B)
    (O : FreshOracle.Oracle (Query:=Query) (E:=E)
      (law (probability B 0) (probability_le_one hB)) σ) :
    ∀ᵐ b ∂law (probability B 0) (probability_le_one hB),∀ q,O.sample q b=O.truth q := by
  have hh : ∀ᵐ b ∂law (probability B 0) (probability_le_one hB),b=true := by
    rw [zero_law hB]
    simp
  filter_upwards [hh] with b hb
  subst b
  exact oracle_true hB O

end Bilevel.BernoulliOracle
