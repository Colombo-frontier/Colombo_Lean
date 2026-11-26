import Bilevel.PartialLegendreEnvelopeComparison
import Bilevel.BernoulliOracle

/-! A fixed conservative sample potential for the actual conjugates.
The common scalar term is unrestricted except for having its stated gradient;
only the informative difference enters the full-gradient variance bound. -/
noncomputable section
open MeasureTheory
namespace Bilevel.PartialLegendre.ConjugateOracle
open PrimitiveGeometry

variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  {δ : NNReal} {G G₀ : Joint X Y → Joint X Y}
  (hG : LipschitzWith δ G) (hG₀ : LipschitzWith δ G₀) (hδ : δ<1)

def meanGradient (m : ℝ) (C : Joint X Y → Joint X Y) (q : Joint X Y) : Joint X Y :=
  m • jointGradient hG hδ q+C q

def sampleGradient (m p : ℝ) (C : Joint X Y → Joint X Y) (b : Bool) (q : Joint X Y) : Joint X Y :=
  BernoulliOracle.sample p (m • jointGradient hG₀ hδ q+C q)
    (m • (jointGradient hG hδ q-jointGradient hG₀ hδ q)) b

def samplePotential (P P₀ Q : Joint X Y → ℝ) (m p : ℝ) (b : Bool) (q : Joint X Y) : ℝ :=
  BernoulliOracle.sample p (m*jointConjugate hG₀ hδ P₀ q+Q q)
    (m*(jointConjugate hG hδ P q-jointConjugate hG₀ hδ P₀ q)) b

omit [CompleteSpace X] in
theorem base_add_signal (m : ℝ) (C : Joint X Y → Joint X Y) (q : Joint X Y) :
    (m • jointGradient hG₀ hδ q+C q)+
      m • (jointGradient hG hδ q-jointGradient hG₀ hδ q)=meanGradient hG hδ m C q := by
  unfold meanGradient
  module

theorem sampleGradient_mean (m p : ℝ) (hp : 0<p) (hp1 : p≤1)
    (C : Joint X Y → Joint X Y) (q : Joint X Y) :
    (∫ b,sampleGradient hG hG₀ hδ m p C b q ∂BernoulliOracle.law p hp1)=
      meanGradient hG hδ m C q := by
  unfold sampleGradient
  rw [BernoulliOracle.sample_mean p hp hp1,base_add_signal]

omit [CompleteSpace X] in
theorem sampleGradient_variance (m p : ℝ) (hp : 0<p) (hp1 : p≤1)
    (C : Joint X Y → Joint X Y) (q : Joint X Y) :
    (∫ b,‖sampleGradient hG hG₀ hδ m p C b q-meanGradient hG hδ m C q‖^2
      ∂BernoulliOracle.law p hp1)=
      (p⁻¹-1)*‖m • (jointGradient hG hδ q-jointGradient hG₀ hδ q)‖^2 := by
  rw [← base_add_signal hG hG₀ hδ m C q]
  exact BernoulliOracle.sample_variance p hp hp1 _ _

omit [CompleteSpace X] in
theorem sampleGradient_variance_bound {m η B σ : ℝ} (hm : 0≤m) (hB : 0<B)
    (hdiff : ∀ v,‖G v-G₀ v‖≤η)
    (henv : (Real.sqrt 2*m/(1-(δ:ℝ)))*η≤B)
    (C : Joint X Y → Joint X Y) (q : Joint X Y) :
    (∫ b,‖sampleGradient hG hG₀ hδ m (BernoulliOracle.probability B σ) C b q-
      meanGradient hG hδ m C q‖^2 ∂BernoulliOracle.law
        (BernoulliOracle.probability B σ) (BernoulliOracle.probability_le_one hB))≤σ^2 := by
  have hs : ‖m • (jointGradient hG hδ q-jointGradient hG₀ hδ q)‖≤B := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hm]
    have hh := mul_le_mul_of_nonneg_left (jointGradient_difference_bound hG hG₀ hδ hdiff q) hm
    apply le_trans _ henv
    convert hh using 1
    ring
  rw [← base_add_signal hG hG₀ hδ m C q]
  exact BernoulliOracle.bounded_variance hB _ _ hs

variable (P P₀ Q : Joint X Y → ℝ) (C : Joint X Y → Joint X Y)
  (hP : ∀ q,HasGradientAt P (G q) q) (hP₀ : ∀ q,HasGradientAt P₀ (G₀ q) q)
  (hQ : ∀ q,HasGradientAt Q (C q) q)
include hP hP₀ hQ

theorem samplePotential_hasGradientAt (m p : ℝ) (b : Bool) (q : Joint X Y) :
    HasGradientAt (samplePotential hG hG₀ hδ P P₀ Q m p b)
      (sampleGradient hG hG₀ hδ m p C b q) q := by
  have hb : HasGradientAt (fun v => m*jointConjugate hG₀ hδ P₀ v+Q v)
      (m • jointGradient hG₀ hδ q+C q) q := by
    apply hasGradientAt_iff_hasFDerivAt.mpr
    have hh := ((jointConjugate_hasGradientAt hG₀ hδ P₀ hP₀ q).hasFDerivAt.const_smul m).add
      (hQ q).hasFDerivAt
    convert hh using 1
    ext v
    simp [InnerProductSpace.toDual_apply,real_inner_smul_left,inner_add_left]
  exact BernoulliOracle.sample_hasGradient hb
    (informative_hasGradientAt hG hG₀ hδ P P₀ hP hP₀ m q) p b

theorem samplePotential_gradient (m p : ℝ) (b : Bool) (q : Joint X Y) :
    gradient (samplePotential hG hG₀ hδ P P₀ Q m p b) q=
      sampleGradient hG hG₀ hδ m p C b q :=
  (samplePotential_hasGradientAt hG hG₀ hδ P P₀ Q C hP hP₀ hQ m p b q).gradient

end Bilevel.PartialLegendre.ConjugateOracle
