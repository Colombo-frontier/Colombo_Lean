import AdaptiveSphereGlobalMean
import ExternalPriorHandleCount
import LowerRisk
import LowerEventMass

open MeasureTheory
open scoped RealInnerProductSpace

namespace Task006.HardFamilyBayes

open Task006.Full Task006.Full.OracleAlgorithm Task006.Full.HardFamily
open Task006.HaarRebalancing Task006.AdaptiveSphereTranscript Task006.AdaptiveSphereGlobal

noncomputable section
variable {d N : ℕ} {S : Type*} [MeasurableSpace S]

def originalOutput (alg : OracleAlgorithm d N S) (j : Fin d)
    (w : Exogenous S × OrthogonalGroup d) : Space d :=
  alg.output w.1.1 (alg.finalTranscript (linearSample id (column w.2 j)) w.1.2 w.1.1)

def originalGap (alg : OracleAlgorithm d N S) (j : Fin d) (R slope : ℝ)
    (w : Exogenous S × OrthogonalGroup d) : ℝ :=
  slope*(R+inner ℝ (column w.2 j) (originalOutput alg j w))

def originalK (alg : OracleAlgorithm d N S) (j : Fin d)
    (w : Exogenous S × OrthogonalGroup d) : ℕ :=
  (alg.informativeHandles (linearSample id (column w.2 j)) w.1.2 w.1.1).card

theorem originalOutput_measurable (alg : OracleAlgorithm d N S) (j : Fin d) :
    Measurable (originalOutput alg j) := by
  have hF : Measurable (fun p : Space d × (Space d × ℝ) => linearSample id p.1 p.2.1 p.2.2) :=
    measurable_snd.snd.mul (measurable_fst.inner measurable_snd.fst)
  have hh := (alg.runPrefix_parameter_measurable (linearSample id) hF N).comp
    (exogenousHaarInput_measurable j)
  have hm := alg.output_measurable.comp (measurable_fst.fst.prodMk hh)
  change Measurable (fun w : Exogenous S × OrthogonalGroup d =>
    alg.output w.1.1 (alg.finalTranscript (linearSample id (column w.2 j)) w.1.2 w.1.1))
  simpa only [Function.comp_def,exogenousHaarInput,finalTranscript] using hm

theorem originalGap_measurable (alg : OracleAlgorithm d N S) (j : Fin d) (R slope : ℝ) :
    Measurable (originalGap alg j R slope) := by
  exact (measurable_const.add (((measurable_column j).comp measurable_snd).inner
    (originalOutput_measurable alg j))).const_mul slope

theorem originalK_measurable (alg : OracleAlgorithm d N S) (j : Fin d) :
    Measurable (fun w => (originalK alg j w : ℝ)) := by
  have hF : Measurable (fun p : Space d × (Space d × ℝ) => linearSample id p.1 p.2.1 p.2.2) :=
    measurable_snd.snd.mul (measurable_fst.inner measurable_snd.fst)
  have hm := (alg.informativeHandles_card_parameter_measurable (linearSample id) hF).comp
    (exogenousHaarInput_measurable j)
  change Measurable (fun w : Exogenous S × OrthogonalGroup d =>
    ((alg.informativeHandles (linearSample id (column w.2 j)) w.1.2 w.1.1).card : ℝ))
  simpa only [Function.comp_def,exogenousHaarInput] using hm

theorem realizedGap_formula (alg : OracleAlgorithm d N S) (L R A : ℝ)
    (hL : 0 ≤ L) (hR : 0 ≤ R) (hA : 16 ≤ A) (θ : Space d) (hθ : ‖θ‖ = 1)
    (z : Exogenous S) :
    alg.realizedGap (instanceOfDirection L R A hL hA θ hθ) z =
      (16*L/A)*(R+inner ℝ θ
        (alg.output z.1 (alg.finalTranscript (linearSample id θ) z.2 z.1))) := by
  rw [realizedGap,objective_formula,optimalValue_formula L R A hL hR hA θ hθ]
  change (16*L/A)*inner ℝ θ (alg.output z.1 (alg.finalTranscript (linearSample id θ) z.2 z.1)) -
    (-(16*L/A)*R) = _
  ring

theorem originalK_integrable (alg : OracleAlgorithm d N S) (j : Fin d)
    (γ : Measure (Exogenous S × OrthogonalGroup d)) [IsFiniteMeasure γ] :
    Integrable (fun w => (originalK alg j w : ℝ)) γ := by
  apply Integrable.of_bound (originalK_measurable alg j).aestronglyMeasurable N
  apply Filter.Eventually.of_forall
  intro w
  rw [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast alg.informativeHandles_card_le (linearSample id (column w.2 j)) w.1.1 w.1.2

theorem originalK_expectation (alg : OracleAlgorithm d N S) (j : Fin d)
    (L A : ℝ) (hL : 0 < L) (hA : 16 ≤ A)
    (σ : Measure S) [IsProbabilityMeasure σ] :
    (∫ w, (originalK alg j w : ℝ)
      ∂(σ.prod (iidHandleLaw (law L A hA))).prod (orthogonalHaarProbability d)) ≤ (4096/A^3)*N := by
  have hi := originalK_integrable alg j
    ((σ.prod (iidHandleLaw (law L A hA))).prod (orthogonalHaarProbability d))
  rw [integral_prod_symm _ hi]
  calc
    _ ≤ ∫ _Q : OrthogonalGroup d, ((4096/A^3)*N) ∂orthogonalHaarProbability d :=
      integral_mono hi.integral_prod_right (integrable_const _) (fun Q =>
        (external_prior_handle_budget alg L A hL hA σ (fun _ => column Q j)
          measurable_const id measurable_id).2)
    _ = _ := by simp

def LegalOriginal (alg : OracleAlgorithm d N S) (R : ℝ) : Prop :=
  ∀ θ : Space d, ‖θ‖ = 1 → ∀ seed tape,
    alg.executionLegal (linearSample id θ) tape seed R

theorem originalOutput_norm_le (alg : OracleAlgorithm d N S) (j : Fin d) (R : ℝ)
    (hlegal : LegalOriginal alg R) (w : Exogenous S × OrthogonalGroup d) :
    ‖originalOutput alg j w‖ ≤ R := by
  have h := (hlegal (column w.2 j) ((orthonormal_column w.2).norm_eq_one j) w.1.1 w.1.2).2.2
  simpa only [originalOutput,outputDomain,Metric.mem_closedBall,dist_zero_right] using h

theorem originalGap_bounds (alg : OracleAlgorithm d N S) (j : Fin d) (R slope : ℝ)
    (hR : 0 ≤ R) (hm : 0 ≤ slope) (hlegal : LegalOriginal alg R)
    (w : Exogenous S × OrthogonalGroup d) :
    0 ≤ originalGap alg j R slope w ∧ originalGap alg j R slope w ≤ 2*slope*R := by
  have hb := (norm_inner_le_norm (𝕜 := ℝ) (column w.2 j) (originalOutput alg j w)).trans
    (mul_le_mul_of_nonneg_left (originalOutput_norm_le alg j R hlegal w) (norm_nonneg _))
  rw [(orthonormal_column w.2).norm_eq_one j,one_mul,Real.norm_eq_abs] at hb
  have hl := (abs_le.mp hb).1
  have hu := (abs_le.mp hb).2
  dsimp only [originalGap]
  constructor <;> nlinarith

theorem originalGap_integrable (alg : OracleAlgorithm d N S) (j : Fin d) (R slope : ℝ)
    (hR : 0 ≤ R) (hm : 0 ≤ slope) (hlegal : LegalOriginal alg R)
    (γ : Measure (Exogenous S × OrthogonalGroup d)) [IsFiniteMeasure γ] :
    Integrable (originalGap alg j R slope) γ := by
  apply Integrable.of_bound (originalGap_measurable alg j R slope).aestronglyMeasurable (2*slope*R)
  apply Filter.Eventually.of_forall
  intro w
  rw [Real.norm_eq_abs,abs_of_nonneg (originalGap_bounds alg j R slope hR hm hlegal w).1]
  exact (originalGap_bounds alg j R slope hR hm hlegal w).2

/-- Uniform fixed-instance guarantees imply the Bayes guarantee under the
genuine independent sphere prior. The prior is introduced only for the proof. -/
theorem fixed_instance_to_bayes_bound (alg : OracleAlgorithm d N S) (j : Fin d)
    (L R A eps : ℝ) (hL : 0 < L) (hR : 0 ≤ R) (hA : 16 ≤ A)
    (σ : Measure S) [IsProbabilityMeasure σ]
    (hsolve : ∀ (θ : Space d) (hθ : ‖θ‖ = 1),
      alg.SolvesInstance eps σ (instanceOfDirection L R A hL.le hA θ hθ)) :
    (∫ w, originalGap alg j R (16*L/A) w
      ∂(σ.prod (iidHandleLaw (law L A hA))).prod (orthogonalHaarProbability d)) ≤ eps := by
  have hlegal : LegalOriginal alg R := by
    intro θ hθ seed tape
    exact (hsolve θ hθ).1 seed tape
  have hm : 0 ≤ 16*L/A := by positivity
  have hi := originalGap_integrable alg j R (16*L/A) hR hm hlegal
    ((σ.prod (iidHandleLaw (law L A hA))).prod (orthogonalHaarProbability d))
  rw [integral_prod_symm _ hi]
  calc
    _ ≤ ∫ _Q : OrthogonalGroup d, eps ∂orthogonalHaarProbability d := by
      apply integral_mono hi.integral_prod_right (integrable_const _)
      intro Q
      have hθ : ‖column Q j‖ = 1 := (orthonormal_column Q).norm_eq_one j
      have hs := (hsolve (column Q j) hθ).2.2
      have heq : (fun z : Exogenous S => originalGap alg j R (16*L/A) (z,Q)) =
          alg.realizedGap (instanceOfDirection L R A hL.le hA (column Q j) hθ) := by
        funext z
        exact (realizedGap_formula alg L R A hL.le hR hA (column Q j) hθ z).symm
      have heint := congrArg (fun f : Exogenous S → ℝ =>
        ∫ z, f z ∂σ.prod (iidHandleLaw (law L A hA))) heq
      exact heint.trans_le hs
    _ = _ := by simp

end
end Task006.HardFamilyBayes
