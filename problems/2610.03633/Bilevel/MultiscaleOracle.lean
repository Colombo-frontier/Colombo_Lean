import Bilevel.MultiscaleSignal
import Bilevel.BernoulliOracle

/-! The source's actual conservative scalar Bernoulli sample potential.
Every sample is C³, its reported vectors are its partial gradients, and the
global mean and variance formulas use the proved informative envelope. -/

noncomputable section
universe u
namespace Bilevel.MultiscaleMean
open CompensatedMean MeasureTheory
open scoped RealInnerProductSpace

def envelopeConstant (_E : Type u) : ℝ := Classical.choose informative_gradient_envelope.{u}

theorem envelopeConstant_one_le (E : Type u) : 1 ≤ envelopeConstant E :=
  (Classical.choose_spec informative_gradient_envelope.{u}).1

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
namespace Parameters
variable {n : ℕ} (P : Parameters (E := E) n)

def signalBound : ℝ := envelopeConstant E*P.μ*P.β^2/P.θ

omit [CompleteSpace E] in
theorem signalBound_pos : 0 < P.signalBound := by
  have hC : 0 < envelopeConstant E := lt_of_lt_of_le zero_lt_one (envelopeConstant_one_le E)
  have hμ := P.μ_pos
  have hβ := P.β_pos
  have hθ : 0 < P.θ := by linarith [P.θ_ge_one]
  dsimp [signalBound]
  positivity

theorem signal_gradient_bound (hscale : P.β*P.θ ≤ 1) (y : LowerSpace E) :
    ‖P.signalY y‖ ≤ P.signalBound :=
  (Classical.choose_spec informative_gradient_envelope).2 E n P hscale y

def inactiveLower (x : E) (y : LowerSpace E) : ℝ := P.data.lower x y-P.signal y
def inactiveLowerY (x : E) (y : LowerSpace E) : LowerSpace E := P.data.lowerY x y-P.signalY y

theorem inactiveLower_hasGradientX (x : E) (y : LowerSpace E) :
    HasGradientAt (fun v => P.inactiveLower v y) (P.data.lowerX x y) x := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  exact (P.data.lower_hasGradientX x y).hasFDerivAt.sub_const (P.signal y)

theorem inactiveLower_hasGradientY (x : E) (y : LowerSpace E) :
    HasGradientAt (P.inactiveLower x) (P.inactiveLowerY x y) y := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  simpa only [inactiveLower,inactiveLowerY,map_sub] using (P.data.lower_hasGradientY x y).hasFDerivAt.sub
    (P.signal_hasGradientAt y).hasFDerivAt

def sampleLower (p : ℝ) (x : E) (y : LowerSpace E) (b : Bool) : ℝ :=
  BernoulliOracle.sample p (P.inactiveLower x y) (P.signal y) b

def sampleLowerY (p : ℝ) (x : E) (y : LowerSpace E) (b : Bool) : LowerSpace E :=
  BernoulliOracle.sample p (P.inactiveLowerY x y) (P.signalY y) b

def sampleLowerX (_p : ℝ) (x : E) (y : LowerSpace E) (_b : Bool) : E := P.data.lowerX x y

theorem sampleLower_hasGradientX (p : ℝ) (x : E) (y : LowerSpace E) (b : Bool) :
    HasGradientAt (fun v => P.sampleLower p v y b) (P.sampleLowerX p x y b) x := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  exact (P.inactiveLower_hasGradientX x y).hasFDerivAt.add_const
    ((if b then p⁻¹ else 0)*P.signal y)

theorem sampleLower_hasGradientY (p : ℝ) (x : E) (y : LowerSpace E) (b : Bool) :
    HasGradientAt (fun v => P.sampleLower p x v b) (P.sampleLowerY p x y b) y :=
  BernoulliOracle.sample_hasGradient (P.inactiveLower_hasGradientY x y) (P.signal_hasGradientAt y) p b

theorem lower_joint_contDiff : ContDiff ℝ 3 (fun v : E × LowerSpace E => P.data.lower v.1 v.2) := by
  have h := (P.data.lower_contDiff 0).comp (contDiff_snd (E := E))
  have hx : ContDiff ℝ 3 (fun v : E × LowerSpace E => v.1) := contDiff_fst
  have hu : ContDiff ℝ 3 (fun v : E × LowerSpace E => uProj E v.2) :=
    (uProj E).contDiff.comp contDiff_snd
  have hh := h.sub ((hx.inner ℝ hu).const_smul P.L)
  convert hh using 1
  funext v
  simp only [CompensatedMean.Data.lower,inner_zero_left,mul_zero,sub_zero,Function.comp_apply,smul_eq_mul]
  change P.μ/2*(‖uProj E v.2‖^2+(sProj E v.2)^2)+P.L/2*(zProj E v.2)^2-
    P.L*⟪v.1,uProj E v.2⟫+P.data.perturbation v.2 = _
  change _ = P.μ/2*(‖uProj E v.2‖^2+(sProj E v.2)^2)+P.L/2*(zProj E v.2)^2+
    P.data.perturbation v.2-P.L*⟪v.1,uProj E v.2⟫
  ring

theorem sampleLower_joint_contDiff (p : ℝ) (b : Bool) :
    ContDiff ℝ 3 (fun v : E × LowerSpace E => P.sampleLower p v.1 v.2 b) :=
  (P.lower_joint_contDiff.sub (P.signal_contDiff.comp contDiff_snd)).add
    (contDiff_const.mul (P.signal_contDiff.comp contDiff_snd))

theorem sampleLower_mean (p : ℝ) (x : E) (y : LowerSpace E) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    (∫ b,P.sampleLower p x y b ∂BernoulliOracle.law p hp1) = P.data.lower x y := by
  have h := BernoulliOracle.sample_mean p hp0 hp1 (P.inactiveLower x y) (P.signal y)
  simpa only [inactiveLower,sub_add_cancel] using h

theorem sampleLowerX_mean (p : ℝ) (x : E) (y : LowerSpace E) (hp1 : p ≤ 1) :
    (∫ b,P.sampleLowerX p x y b ∂BernoulliOracle.law p hp1) = P.data.lowerX x y := by
  simp only [sampleLowerX,integral_const,measureReal_def,measure_univ,ENNReal.toReal_one,one_smul]

theorem sampleLowerY_mean (p : ℝ) (x : E) (y : LowerSpace E) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    (∫ b,P.sampleLowerY p x y b ∂BernoulliOracle.law p hp1) = P.data.lowerY x y := by
  have h := BernoulliOracle.sample_mean p hp0 hp1 (P.inactiveLowerY x y) (P.signalY y)
  simpa only [inactiveLowerY,sub_add_cancel] using h

def activationProbability (σ : ℝ) : ℝ := BernoulliOracle.probability P.signalBound σ

omit [CompleteSpace E] in
theorem activationProbability_pos (σ : ℝ) : 0 < P.activationProbability σ :=
  BernoulliOracle.probability_pos P.signalBound_pos

omit [CompleteSpace E] in
theorem activationProbability_le_one (σ : ℝ) : P.activationProbability σ ≤ 1 :=
  BernoulliOracle.probability_le_one P.signalBound_pos

omit [CompleteSpace E] in
theorem inverse_activationProbability (σ : ℝ) :
    (P.activationProbability σ)⁻¹ = 1+σ^2/P.signalBound^2 :=
  BernoulliOracle.inverse_probability P.signalBound_pos

theorem sampleLowerY_variance_exact (p : ℝ) (x : E) (y : LowerSpace E) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    (∫ b,‖P.sampleLowerY p x y b-P.data.lowerY x y‖^2 ∂BernoulliOracle.law p hp1) =
      (p⁻¹-1)*‖P.signalY y‖^2 := by
  have h := BernoulliOracle.sample_variance p hp0 hp1 (P.inactiveLowerY x y) (P.signalY y)
  simpa only [inactiveLowerY,sub_add_cancel] using h

theorem sampleLowerY_variance (σ : ℝ) (x : E) (y : LowerSpace E) (hscale : P.β*P.θ ≤ 1) :
    (∫ b,‖P.sampleLowerY (P.activationProbability σ) x y b-P.data.lowerY x y‖^2
      ∂BernoulliOracle.law (P.activationProbability σ) (P.activationProbability_le_one σ)) ≤ σ^2 := by
  have h := BernoulliOracle.bounded_variance P.signalBound_pos (P.inactiveLowerY x y) (P.signalY y)
    (P.signal_gradient_bound hscale y) (σ := σ)
  simpa only [inactiveLowerY,sub_add_cancel] using h

theorem sampleLower_full_variance (σ : ℝ) (x : E) (y : LowerSpace E) (hscale : P.β*P.θ ≤ 1) :
    (∫ b,(‖P.sampleLowerX (P.activationProbability σ) x y b-P.data.lowerX x y‖^2+
      ‖P.sampleLowerY (P.activationProbability σ) x y b-P.data.lowerY x y‖^2)
      ∂BernoulliOracle.law (P.activationProbability σ) (P.activationProbability_le_one σ)) ≤ σ^2 := by
  simpa only [sampleLowerX,sub_self,norm_zero,zero_pow (by decide : 2 ≠ 0),zero_add] using
    P.sampleLowerY_variance σ x y hscale

theorem inactive_sample (p : ℝ) (x : E) (y : LowerSpace E) :
    P.sampleLower p x y false = P.inactiveLower x y ∧
    P.sampleLowerY p x y false = P.inactiveLowerY x y := by
  simp [sampleLower,sampleLowerY,BernoulliOracle.sample]

end Parameters
end Bilevel.MultiscaleMean
