import HeavyTail.ConfidenceModel
import HeavyTail.AdaptiveSamplerTesting
import HeavyTail.ModelQuantile

/-! The calibrated confidence lower bound for the full public/private model and
its actual nested fresh-kernel execution. The arbitrary seed is part of the
public policy and cannot depend on the hidden Boolean hypothesis. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace
namespace HeavyTail

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem confidence_model_probability_lower (θ : OracleParameters) (e : E) (he : ‖e‖ = 1)
    (a u : ℝ) (ha : 0 ≤ a) (haG : a ≤ θ.G) (hu0 : 0 < u) (hu1 : u < 1)
    (hbudget : a ^ θ.p * (u + u ^ θ.p / (1 - u) ^ (θ.p - 1)) ≤ θ.s ^ θ.p)
    (A : PublicPolicy (quadraticPublicProblem E θ)) :
    ∃ h : Bool, u ^ θ.T / 2 ≤
      (PublicPolicy.outputLaw A (confidencePrivateInstance θ e he a u ha haG hu0 hu1 hbudget h)).real
        {x | ENNReal.ofReal (envelope θ.μ θ.D a) ≤
          (confidencePrivateInstance θ e he a u ha haG hu0 hu1 hbudget h).loss x} := by
  let ν := (erasureCoin u hu1.le).toMeasure
  let I := confidencePrivateInstance θ e he a u ha haG hu0 hu1 hbudget
  let F : Bool → (quadraticPublicProblem E θ).X × Bool → E :=
    fun h z => confidenceOracle e a (envelopeRadius θ.μ θ.D a) u h z.1 z.2
  have hF (h : Bool) : Measurable (F h) :=
    (confidenceOracle_measurable e a _ u h).comp
      ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)
  have hK (h : Bool) : (I h).oracle = kernelOfSampler ν (F h) (hF h) := by
    ext x s hs
    rfl
  let d : AdaptiveKernel.History A.Seed E θ.T → Bool :=
    fun ω => confidenceDecode e (A.strategy.output ω)
  have hd : Measurable d := (confidenceDecode_measurable e).comp
    (measurable_subtype_coe.comp A.strategy.output_measurable)
  have hpair := AdaptiveKernel.sampler_pair_testing_lower A.strategy A.seedLaw ν
    (hF false) (hF true) {true} (by
      intro x z hz
      have hz' : z = true := hz
      simp [F, hz', confidenceOracle, vectorErasureReply]) d hd false
  have hcoin : ν.real {true} = u := by
    simp [ν, measureReal_def, PMF.toMeasure_apply_singleton, erasureCoin,
      PMF.bernoulli_apply, ENNReal.toReal_ofReal hu0.le]
  rw [hcoin, ← hK false, ← hK true] at hpair
  let err : Bool → ℝ := fun h => (A.strategy.historyLaw A.seedLaw (I h).oracle θ.T).real
    {ω | d ω ≠ h}
  have hp : u ^ θ.T ≤ err false + err true := hpair
  have hex : ∃ h : Bool, u ^ θ.T / 2 ≤ err h := by
    by_cases hf : u ^ θ.T / 2 ≤ err false
    · exact ⟨false, hf⟩
    · exact ⟨true, by linarith only [hp, hf]⟩
  obtain ⟨h, hh⟩ := hex
  refine ⟨h, hh.trans ?_⟩
  have herr : err h = (PublicPolicy.outputLaw A (I h)).real
      {x | confidenceDecode e (x : E) ≠ h} := by
    symm
    apply map_measureReal_apply A.strategy.output_measurable
    exact (((confidenceDecode_measurable e).comp measurable_subtype_coe)
      (MeasurableSet.singleton h)).compl
  rw [herr]
  apply measureReal_mono (μ := PublicPolicy.outputLaw A (I h)) _ (measure_ne_top _ _)
  intro x hx
  change ENNReal.ofReal (envelope θ.μ θ.D a) ≤
    (confidencePrivateInstance θ e he a u ha haG hu0 hu1 hbudget h).loss x
  rw [confidencePrivateInstance_loss (E := E) θ e he a u ha haG hu0 hu1 hbudget h x]
  exact ENNReal.ofReal_le_ofReal
    (confidence_wrong_objective_gap (E := E) e he θ.μ_nonneg θ.D_pos.le ha h x hx)

/-- The confidence term is a lower bound on the full-model minimax quantile,
not merely on a separately postulated family experiment. -/
theorem confidence_fixedCallMinimax_lower (θ : OracleParameters) (e : E) (he : ‖e‖ = 1)
    (hT : 0 < θ.T) :
    ENNReal.ofReal (confidenceRate θ.μ θ.D θ.G θ.s θ.p θ.δ θ.T) ≤ fixedCallMinimax E θ := by
  have hz : 0 < erasureLog θ.δ / θ.T :=
    div_pos (erasureLog_pos θ.δ_pos θ.δ_lt_tenth) (Nat.cast_pos.mpr hT)
  let a := tunedConfidenceAmplitude θ.G θ.s θ.p θ.δ θ.T
  let u := tunedErasure θ.δ θ.T
  have ha : 0 ≤ a := confidenceAmplitude_nonneg θ.G_pos.le θ.s_pos.le hz.le
  have haG : a ≤ θ.G := min_le_left _ _
  have hu0 : 0 < u := tunedErasure_pos _ _
  have hu1 : u < 1 := tunedErasure_lt_one θ.δ_pos θ.δ_lt_tenth hT
  have hbudget : a ^ θ.p * (u + u ^ θ.p / (1 - u) ^ (θ.p - 1)) ≤ θ.s ^ θ.p :=
    confidenceAmplitude_moment θ.G_pos.le θ.s_pos.le θ.p_gt_one θ.p_le_two hz
  have hrate : confidenceRate θ.μ θ.D θ.G θ.s θ.p θ.δ θ.T ≤ envelope θ.μ θ.D a :=
    confidenceAmplitude_envelope θ.μ_nonneg θ.D_pos.le θ.G_pos.le θ.s_pos.le
      θ.p_gt_one θ.δ_pos θ.δ_lt_tenth hT
  apply fixedCallMinimax_lower (E := E)
  intro A
  obtain ⟨h, hh⟩ := confidence_model_probability_lower θ e he a u ha haG hu0 hu1 hbudget
    (A (quadraticPublicProblem E θ))
  refine ⟨quadraticPublicProblem E θ,
    confidencePrivateInstance θ e he a u ha haG hu0 hu1 hbudget h, ?_⟩
  have hmass : u ^ θ.T / 2 = 2 * θ.δ := by
    dsimp [u, tunedErasure]
    rw [confidence_erasure_probability θ.δ_pos hT]
    ring
  rw [hmass] at hh
  apply (show θ.δ < 2 * θ.δ by linarith only [θ.δ_pos]).trans_le
  exact hh.trans (measureReal_mono (fun x hx => (ENNReal.ofReal_le_ofReal hrate).trans hx)
    (measure_ne_top _ _))

end HeavyTail
