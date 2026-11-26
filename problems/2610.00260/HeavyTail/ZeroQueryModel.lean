import HeavyTail.ConfidenceModel
import HeavyTail.ModelQuantile
import HeavyTail.FeasibleOracleModel

/-! The public proximal cap and the matching zero-query lower bound in the
extended-valued full model. The upper output is public and always lies in the
effective domain, even when the initial point does not. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace
namespace HeavyTail

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  {θ : OracleParameters}

def PublicProblem.zeroQueryOutput (B : PublicProblem E θ) : B.X :=
  ⟨B.prox.point (zeroQueryStep θ.μ θ.D θ.G) B.initial,
    B.domain_subset (B.prox.feasible _ (zeroQueryStep_pos θ.μ_nonneg θ.D_pos θ.G_pos) _)⟩

theorem PublicProblem.zeroQueryOutput_domain (B : PublicProblem E θ) :
    (B.zeroQueryOutput : E) ∈ B.S :=
  B.prox.feasible _ (zeroQueryStep_pos θ.μ_nonneg θ.D_pos θ.G_pos) _

theorem PrivateInstance.zeroQueryOutput_loss {B : PublicProblem E θ} (I : PrivateInstance B) :
    I.loss B.zeroQueryOutput ≤ ENNReal.ofReal (2 * envelope θ.μ θ.D θ.G) := by
  rw [I.loss_of_mem B.zeroQueryOutput B.zeroQueryOutput_domain]
  apply ENNReal.ofReal_le_ofReal
  exact (zero_query_envelope_cap B.prox B.h_strongConvex θ.μ_nonneg θ.D_pos θ.G_pos
    B.initial I.minimizer I.minimizer_domain I.initial_distance (fun u hu =>
      I.lipschitz_difference u (B.domain_subset hu) I.minimizer
        (B.domain_subset I.minimizer_domain))).2

theorem PublicPolicy.outputLaw_constant {B : PublicProblem E θ}
    (x : B.X) (I : PrivateInstance B) :
    PublicPolicy.outputLaw (PublicPolicy.constant B x) I = Measure.dirac x := by
  change (AdaptiveKernel.Policy.historyLaw
    (AdaptiveKernel.RandomizedPolicy.constant (T := θ.T) x x).strategy
    (AdaptiveKernel.RandomizedPolicy.constant (T := θ.T) x x).seedLaw I.oracle θ.T).map
      (fun _ => x) = _
  rw [Measure.map_const, measure_univ, one_smul]

/-- This public output uses no oracle information. Padding it to any fixed raw
budget preserves the output and yields the manuscript's deterministic cap. -/
theorem zero_query_fixedCallMinimax_cap (θ : OracleParameters) :
    fixedCallMinimax E θ ≤ ENNReal.ofReal (2 * envelope θ.μ θ.D θ.G) := by
  apply fixedCallMinimax_upper (E := E) (fun B => PublicPolicy.constant B B.zeroQueryOutput)
  intro B I
  rw [PublicPolicy.outputLaw_constant]
  have hn : B.zeroQueryOutput ∉ {x | ENNReal.ofReal (2 * envelope θ.μ θ.D θ.G) < I.loss x} :=
    not_lt_of_ge I.zeroQueryOutput_loss
  rw [measureReal_def, Measure.dirac_apply, Set.indicator_of_not_mem hn, ENNReal.toReal_zero]
  exact θ.δ_pos.le

/-- A noiseless member of the binary hard family is admissible for every
positive strong and weak moment budget. -/
def deterministicConfidencePrivateInstance (θ : OracleParameters) (e : E) (he : ‖e‖ = 1)
    (h : Bool) : PrivateInstance (quadraticPublicProblem E θ) where
  f := confidenceLoss e θ.G (envelopeRadius θ.μ θ.D θ.G) h
  f_convex := confidenceLoss_convex e θ.G_pos.le _ h
  f_lipschitz := (confidenceLoss_lipschitz e he θ.G_pos.le _ h).lipschitzOnWith
  oracle := Kernel.deterministic
    (fun x : (quadraticPublicProblem E θ).X => confidenceMean e θ.G (envelopeRadius θ.μ θ.D θ.G) h x)
    ((confidenceMean_measurable e θ.G _ h).comp measurable_subtype_coe)
  oracle_probability := by infer_instance
  reply_integrable _ := integrable_dirac
  mean_subgradient x y _ := by
    simp only [Kernel.deterministic_apply, integral_dirac, inner_sub_right]
    have hg := confidenceMean_subgradient e θ.G_pos.le (envelopeRadius θ.μ θ.D θ.G) h x y
    rw [inner_sub_right] at hg
    linarith only [hg]
  noise_memLp x := by
    simp only [Kernel.deterministic_apply, integral_dirac]
    apply (memLp_congr_ae (g := fun _ => (0 : E)) (by simp [Filter.EventuallyEq])).mpr
    exact memLp_const 0
  strong_moment x := by
    simp only [Kernel.deterministic_apply, integral_dirac, sub_self, norm_zero]
    rw [Real.zero_rpow (by linarith only [θ.p_gt_one] : θ.p ≠ 0)]
    exact Real.rpow_nonneg (θ.s_pos.le.trans θ.s_le_L) _
  weak_moment x v _ := by
    simp only [Kernel.deterministic_apply, integral_dirac, sub_self, inner_zero_right, abs_zero]
    rw [Real.zero_rpow (by linarith only [θ.p_gt_one] : θ.p ≠ 0)]
    exact Real.rpow_nonneg θ.s_pos.le _
  minimizer := confidenceCenter e (envelopeRadius θ.μ θ.D θ.G) h
  minimizer_domain := Set.mem_univ _
  minimizing y _ := confidenceObjective_minimizer e he θ.μ_nonneg
    (envelopeRadius_nonneg θ.μ_nonneg θ.D_pos.le θ.G_pos.le)
    (signRadius_curvature_le θ.μ_nonneg θ.G_pos.le) h y
  initial_distance := by
    change ‖0 - confidenceCenter e (envelopeRadius θ.μ θ.D θ.G) h‖ ≤ θ.D
    simpa only [zero_sub, norm_neg] using
      confidenceCenter_initialization e he θ.μ_nonneg θ.D_pos.le θ.G_pos.le h

theorem deterministicConfidencePrivateInstance_loss (θ : OracleParameters)
    (e : E) (he : ‖e‖ = 1) (h : Bool) (x : (quadraticPublicProblem E θ).X) :
    (deterministicConfidencePrivateInstance θ e he h).loss x =
      ENNReal.ofReal (confidenceObjective e θ.G θ.μ (envelopeRadius θ.μ θ.D θ.G) h x -
        confidenceObjective e θ.G θ.μ (envelopeRadius θ.μ θ.D θ.G) h
          (confidenceCenter e (envelopeRadius θ.μ θ.D θ.G) h)) := by
  simp only [PrivateInstance.loss, quadraticPublicProblem_S, Set.mem_univ, if_true]
  rfl

theorem PublicPolicy.outputLaw_zero_independent {B : PublicProblem E θ}
    (A : PublicPolicy B) (hT : θ.T = 0) (I J : PrivateInstance B) :
    PublicPolicy.outputLaw A I = PublicPolicy.outputLaw A J := by
    have hh : A.strategy.historyLaw A.seedLaw I.oracle θ.T =
        A.strategy.historyLaw A.seedLaw J.oracle θ.T := by
      have hzero (n : ℕ) (hn : n = 0) :
          A.strategy.historyLaw A.seedLaw I.oracle n =
            A.strategy.historyLaw A.seedLaw J.oracle n := by
        subst n
        rfl
      exact hzero θ.T hT
    exact congrArg (fun μ => μ.map A.strategy.output) hh

theorem zero_query_binary_family_lower {B : PublicProblem E θ}
    (I : Bool → PrivateInstance B) (decode : B.X → Bool) (hd : Measurable decode)
    (α : ℝ≥0∞) (hgap : ∀ h x, decode x ≠ h → α ≤ (I h).loss x)
    (hT : θ.T = 0) (A : PublicPolicy B) :
    ∃ h, θ.δ < (PublicPolicy.outputLaw A (I h)).real {x | α ≤ (I h).loss x} := by
  obtain ⟨h, hh⟩ := measurable_binary_testing_half (PublicPolicy.outputLaw A (I false)) decode hd
  refine ⟨h, ?_⟩
  have hδ : θ.δ < 1 / 2 := θ.δ_lt_tenth.trans (by norm_num)
  apply hδ.trans_le
  rw [A.outputLaw_zero_independent hT (I false) (I h)] at hh
  apply hh.trans
  exact measureReal_mono (fun x hx => hgap h x hx) (measure_ne_top _ _)

theorem confidence_zero_query_fixedCallMinimax_lower (θ : OracleParameters)
    (e : E) (he : ‖e‖ = 1) (hT : θ.T = 0) :
    ENNReal.ofReal (envelope θ.μ θ.D θ.G) ≤ fixedCallMinimax E θ := by
  have hgap (h : Bool) (x : (quadraticPublicProblem E θ).X)
      (hx : confidenceDecode e (x : E) ≠ h) :
      ENNReal.ofReal (envelope θ.μ θ.D θ.G) ≤
        (deterministicConfidencePrivateInstance θ e he h).loss x := by
    rw [deterministicConfidencePrivateInstance_loss (E := E) θ e he h x]
    exact ENNReal.ofReal_le_ofReal
      (confidence_wrong_objective_gap (E := E) e he θ.μ_nonneg θ.D_pos.le θ.G_pos.le h x hx)
  apply fixedCallMinimax_lower (E := E)
  intro A
  obtain ⟨h, hh⟩ := zero_query_binary_family_lower
    (deterministicConfidencePrivateInstance θ e he)
    (fun x => confidenceDecode e (x : E))
    ((confidenceDecode_measurable e).comp measurable_subtype_coe)
    (ENNReal.ofReal (envelope θ.μ θ.D θ.G)) hgap hT (A (quadraticPublicProblem E θ))
  exact ⟨quadraticPublicProblem E θ, deterministicConfidencePrivateInstance θ e he h, hh⟩

end HeavyTail
