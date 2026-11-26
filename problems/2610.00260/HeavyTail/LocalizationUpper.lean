import HeavyTail.LocalizationAlgorithm
import HeavyTail.PublicStageAlgorithm

/-! Strongly convex upper branch for the full private-instance model.
The small warm-radius case uses one actual stage; the other case uses the
complete public dyadic localization schedule. Constants depend only on p. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal Classical
namespace HeavyTail
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {θ : OracleParameters}

def localizationMultiplier (p : ℝ) : ℝ :=
  localizationTerminalMultiplier (1 - 1 / p)
    (localizationBudgetConstant (1 - 1 / p) (acceptedStageConstant p))

def localizationUpperConstant (p : ℝ) : ℝ :=
  16 * acceptedStageConstant p * localizationMultiplier p + 2 * (localizationMultiplier p) ^ 2

theorem localizationMultiplier_ge_one (p : ℝ) : 1 ≤ localizationMultiplier p :=
  (localizationTerminalMultiplier_bounds
    ((by norm_num : (1 : ℝ) ≤ 2).trans
      (localizationBudgetConstant_bounds (acceptedStageConstant_pos p).le).1)).1

theorem localizationUpperConstant_pos (p : ℝ) : 0 < localizationUpperConstant p := by
  have hC := acceptedStageConstant_pos p
  have hM := zero_lt_one.trans_le (localizationMultiplier_ge_one p)
  unfold localizationUpperConstant
  positivity

theorem warmStartRadius_le (hμ : 0 < θ.μ) :
    warmStartRadius θ.μ θ.D θ.G ≤ Real.sqrt 2 * θ.G / θ.μ := by
  unfold warmStartRadius
  split_ifs with h
  · have hroot : (1 : ℝ) ≤ Real.sqrt 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
    apply (le_div_iff₀ hμ).mpr
    nlinarith only [h, mul_le_mul_of_nonneg_right hroot θ.G_pos.le]
  · exact le_rfl

theorem PublicProblem.public_localized_upper (B : PublicProblem E θ)
    (hμ : 0 < θ.μ) {τ : ℝ} (hτ : 64 * (4 * θ.G + θ.L) ≤ τ)
    (hbudget : 8 * confidenceLog θ.δ ≤ θ.T) :
    ∃ A : PublicPolicy B, ∀ I : PrivateInstance B,
      (PublicPolicy.outputLaw A I).real
        {x | ENNReal.ofReal (localizationUpperConstant θ.p *
          ((fixedThresholdAmplitude θ.G θ.L θ.s θ.p θ.δ τ θ.T) ^ 2 / θ.μ)) < I.loss x} ≤ θ.δ := by
  let R₀ := warmStartRadius θ.μ θ.D θ.G
  let v := fixedThresholdAmplitude θ.G θ.L θ.s θ.p θ.δ τ θ.T
  let M := localizationMultiplier θ.p
  let C₀ := acceptedStageConstant θ.p
  have hR₀ : 0 < R₀ := warmStartRadius_pos hμ θ.D_pos θ.G_pos
  have hwarm : R₀ ≤ Real.sqrt 2 * θ.G / θ.μ := warmStartRadius_le hμ
  have hL : 0 < θ.L := θ.s_pos.trans_le θ.s_le_L
  have hG := θ.G_pos
  have hτpos : 0 < τ := (by positivity : 0 < 64 * (4 * θ.G + θ.L)).trans_le hτ
  have hT : 0 < θ.T := by
    have hh := accepted_round_count_bounds (confidenceLog_ge_one θ.δ_pos θ.δ_lt_tenth) hbudget
    omega
  have hv : 0 < v := (fixedThresholdAmplitude_components θ hτpos hT).1
  have hC₀ : 0 < C₀ := acceptedStageConstant_pos θ.p
  have hM : 0 < M := zero_lt_one.trans_le (localizationMultiplier_ge_one θ.p)
  have hc₀ : ∀ I : PrivateInstance B, ‖(B.warmCenter : E) - I.minimizer‖ ≤ R₀ :=
    fun I => I.warmCenter_radius hμ
  have hClarge : 2 * M ^ 2 ≤ localizationUpperConstant θ.p := by
    change 2 * M ^ 2 ≤ 16 * C₀ * M + 2 * M ^ 2
    exact le_add_of_nonneg_left (by positivity)
  have hCsmall : 16 * C₀ * M ≤ localizationUpperConstant θ.p := by
    change 16 * C₀ * M ≤ 16 * C₀ * M + 2 * M ^ 2
    nlinarith only [sq_nonneg M]
  by_cases hstart : 2 * (M * v / θ.μ) ≤ R₀
  · obtain ⟨J, hJ, hlo, hhi, hcost⟩ := exists_fixedThreshold_forward_schedule θ hμ hT hτpos
      hC₀.le hwarm hstart
    change M * v / θ.μ ≤ finalLocalizationRadius R₀ J at hlo
    change finalLocalizationRadius R₀ J < 2 * (M * v / θ.μ) at hhi
    have hterminal : M * v ≤ θ.μ * finalLocalizationRadius R₀ J := by
      have hh := (div_le_iff₀ hμ).mp hlo
      nlinarith only [hh]
    obtain ⟨A, hA⟩ := B.public_localization_phases hμ hT hτ hR₀ hwarm B.warmCenter hc₀ hJ hterminal hcost
    refine ⟨A, ?_⟩
    intro I
    have hR : 0 ≤ finalLocalizationRadius R₀ J := (div_pos (mul_pos hM hv) hμ).le.trans hlo
    have hsquare := pow_le_pow_left₀ hR hhi.le 2
    have herr : θ.μ / 2 * (finalLocalizationRadius R₀ J) ^ 2 ≤
        2 * M ^ 2 * (v ^ 2 / θ.μ) := by
      have hh := mul_le_mul_of_nonneg_left hsquare (by positivity : 0 ≤ θ.μ / 2)
      have he : θ.μ / 2 * (2 * (M * v / θ.μ)) ^ 2 = 2 * M ^ 2 * (v ^ 2 / θ.μ) := by
        field_simp
        <;> ring
      rwa [he] at hh
    have herr' := herr.trans (mul_le_mul_of_nonneg_right hClarge (by positivity : 0 ≤ v ^ 2 / θ.μ))
    exact (measureReal_mono (fun x hx => lt_of_le_of_lt (ENNReal.ofReal_le_ofReal herr') hx)).trans (hA I)
  · obtain ⟨A, hA⟩ := B.public_stage_at_budget hτ hR₀ B.warmCenter hc₀ hbudget
    refine ⟨A, ?_⟩
    intro I
    have hh := mul_le_mul_of_nonneg_right (le_of_not_ge hstart) (by positivity : 0 ≤ 8 * C₀ * v)
    have herr : 8 * C₀ * R₀ * v ≤ 16 * C₀ * M * (v ^ 2 / θ.μ) := by
      convert hh using 1 <;> ring
    have herr' := herr.trans (mul_le_mul_of_nonneg_right hCsmall (by positivity : 0 ≤ v ^ 2 / θ.μ))
    exact (measureReal_mono (fun x hx => lt_of_le_of_lt (ENNReal.ofReal_le_ofReal herr') hx)).trans (hA I)

theorem localized_fixedCallMinimax_upper (hμ : 0 < θ.μ) {τ : ℝ}
    (hτ : 64 * (4 * θ.G + θ.L) ≤ τ)
    (hbudget : 8 * confidenceLog θ.δ ≤ θ.T) :
    fixedCallMinimax E θ ≤ ENNReal.ofReal (localizationUpperConstant θ.p *
      ((fixedThresholdAmplitude θ.G θ.L θ.s θ.p θ.δ τ θ.T) ^ 2 / θ.μ)) := by
  apply fixedCallMinimax_upper_of_public_policies
  intro B
  exact B.public_localized_upper hμ hτ hbudget

end HeavyTail
