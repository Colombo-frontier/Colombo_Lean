import Smoothness2601.SineScaling
import Smoothness2601.WrappedProfiles
import Smoothness2601.Minimax

/-! All hard-instance numerical constants precede the regularity cap,
accuracy, dimension, and orthonormal frame. -/
noncomputable section
namespace Smoothness2601.HardProfiles

structure WidthConstants (b : Budgets) (M Λ β : ℝ) where
  m : ℝ
  c : ℝ
  τ : ℝ
  K : ℝ
  m_gt : b.μ < m
  m_lt : m < b.L₁
  c_pos : 0 < c
  c_le : c ≤ b.L₀
  τ_pos : 0 < τ
  K_pos : 0 < K
  upper : τ*upperSmoothness ≤ b.L₁
  lower : (m/c)*τ*K*frontierSmoothness ≤ (b.L₁-m)/2
  mixed : (m/c)*(τ*frontierSmoothness+Cutoffs.frontierGradientBound/K) ≤ b.L₂
  yy : (m/c)*(Cutoffs.frontierGradientBound/K+(1/4)/(τ*K^2)) ≤ b.L₂
  envelope_ratio : Real.exp 1^β/(K*Λ) ≤ 1
  envelope_scale : ((m/c)*(Cutoffs.frontierGradientBound+1/4))*(Real.exp 1^β/(K*Λ)) ≤ M*Λ

theorem widthConstants_nonempty (b : Budgets) (hgap : b.μ < b.L₁)
    {M Λ β : ℝ} (hM : 0 < M) (hΛ : 0 < Λ) : Nonempty (WidthConstants b M Λ β) := by
  obtain ⟨m,c,τ,K,hmμ,hmL,hc,hcL,hτ,hK,hu,hl,hxy,hyy,he,he'⟩ :=
    exists_uniform_width_constants (β := β) b hgap upperSmoothness_nonneg
      (by norm_num : (0:ℝ) ≤ 1/4) ExtensiveChain.frontierGradientBound_nonneg
      frontierSmoothness_nonneg hM hΛ
  exact ⟨⟨m,c,τ,K,hmμ,hmL,hc,hcL,hτ,hK,hu,hl,hxy,hyy,he,he'⟩⟩

namespace WidthConstants
variable {b : Budgets} {M Λ β : ℝ} (W : WidthConstants b M Λ β)

theorem m_pos : 0 < W.m := b.μ_pos.trans W.m_gt

def signalConstant : ℝ := (W.m/W.c)*(Cutoffs.frontierGradientBound+(1/4)/(W.τ*W.K))

theorem signalConstant_pos : 0 < W.signalConstant := by
  unfold signalConstant
  exact mul_pos (div_pos W.m_pos W.c_pos)
    (add_pos_of_nonneg_of_pos ExtensiveChain.frontierGradientBound_nonneg (by
      have := W.τ_pos
      have := W.K_pos
      positivity))

theorem baseline_threshold : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
    ∀ s h : ℝ, 0 < s → s ≤ δ → 0 < h → W.K*s ≤ h → h ≤ W.K →
      b.μ ≤ W.m-(W.m/W.c)*(s^2/(W.τ*h))*(1/4) ∧
      W.m+(W.m/W.c)*(W.τ*h*frontierSmoothness+2*s*Cutoffs.frontierGradientBound+
        (s^2/(W.τ*h))*(1/4)) ≤ b.L₁ ∧
      (W.m/W.c)*(W.τ*frontierSmoothness+(s/h)*Cutoffs.frontierGradientBound) ≤ b.L₂ ∧
      (W.m/W.c)*((s/h)*Cutoffs.frontierGradientBound+(s^2/(W.τ*h^2))*(1/4)) ≤ b.L₂ :=
  exists_baseline_threshold W.m_gt W.m_lt W.c_pos W.τ_pos W.K_pos
    (by norm_num) ExtensiveChain.frontierGradientBound_nonneg frontierSmoothness_nonneg W.lower W.mixed W.yy

def baselineThreshold : ℝ := Classical.choose W.baseline_threshold

theorem baselineThreshold_spec : 0 < W.baselineThreshold ∧ W.baselineThreshold ≤ 1 ∧
    ∀ s h : ℝ, 0 < s → s ≤ W.baselineThreshold → 0 < h → W.K*s ≤ h → h ≤ W.K →
      b.μ ≤ W.m-(W.m/W.c)*(s^2/(W.τ*h))*(1/4) ∧
      W.m+(W.m/W.c)*(W.τ*h*frontierSmoothness+2*s*Cutoffs.frontierGradientBound+
        (s^2/(W.τ*h))*(1/4)) ≤ b.L₁ ∧
      (W.m/W.c)*(W.τ*frontierSmoothness+(s/h)*Cutoffs.frontierGradientBound) ≤ b.L₂ ∧
      (W.m/W.c)*((s/h)*Cutoffs.frontierGradientBound+(s^2/(W.τ*h^2))*(1/4)) ≤ b.L₂ :=
  Classical.choose_spec W.baseline_threshold

def threshold : ℝ := min W.baselineThreshold
  (min (W.τ^2*W.K^2/((2:ℝ)^β)^2)
    (min (W.τ*W.c*W.K/(Cutoffs.frontierGradientBound+1))
      (b.σ/(W.signalConstant*W.K+1))))

theorem threshold_pos : 0 < W.threshold := by
  have := W.baselineThreshold_spec.1
  have := W.τ_pos
  have := W.c_pos
  have := W.K_pos
  have := W.signalConstant_pos
  have := ExtensiveChain.frontierGradientBound_nonneg
  have := b.σ_pos
  unfold threshold
  positivity

theorem threshold_conditions {s : ℝ} (hs : s ≤ W.threshold) :
    s ≤ W.baselineThreshold ∧ s ≤ 1 ∧
    s ≤ W.τ^2*W.K^2/((2:ℝ)^β)^2 ∧
    s ≤ W.τ*W.c*W.K/(Cutoffs.frontierGradientBound+1) ∧
    s ≤ b.σ/(W.signalConstant*W.K+1) := by
  have hb : s ≤ W.baselineThreshold := hs.trans (min_le_left _ _)
  have ht := hs.trans (min_le_right _ _)
  have hu := ht.trans (min_le_right _ _)
  exact ⟨hb,hb.trans W.baselineThreshold_spec.2.1,
    ht.trans (min_le_left _ _),hu.trans (min_le_left _ _),hu.trans (min_le_right _ _)⟩

theorem signal_small {s h : ℝ} (hs : 0 < s) (hsδ : s ≤ W.threshold)
    (hu : h ≤ W.K) : W.signalConstant*s*h ≤ b.σ := by
  have hb := (le_div_iff₀ (by have := W.signalConstant_pos; have := W.K_pos; positivity :
    0 < W.signalConstant*W.K+1)).mp (W.threshold_conditions hsδ).2.2.2.2
  have hh := mul_le_mul_of_nonneg_left hu (mul_nonneg W.signalConstant_pos.le hs.le)
  nlinarith

theorem theta_small {s h : ℝ} (hs : 0 < s) (hsδ : s ≤ W.threshold)
    (hh : 0 < h) (hl : W.K*s ≤ h) :
    |(s^2/(W.τ*W.c))/h| * (1/4) ≤ 1/4 ∧
    2*((s^2/(W.τ*W.c))/h)^2*(1/4)^2*Cutoffs.frontierGradientBound ≤ 1/4 := by
  have hτ := W.τ_pos
  have hc := W.c_pos
  have hK := W.K_pos
  have hC := ExtensiveChain.frontierGradientBound_nonneg
  let r := (s^2/(W.τ*W.c))/h
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hrb : r ≤ s/(W.τ*W.c*W.K) := by
    dsimp [r]
    rw [div_div]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hm := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ s*W.τ*W.c)
    nlinarith only [hm]
  have hsC := (le_div_iff₀ (by positivity : 0 < Cutoffs.frontierGradientBound+1)).mp
    (W.threshold_conditions hsδ).2.2.2.1
  have hrC : r*(Cutoffs.frontierGradientBound+1) ≤ 1 := by
    have hr' := (le_div_iff₀ (by positivity : 0 < W.τ*W.c*W.K)).mp hrb
    have hm := mul_le_mul_of_nonneg_right hr' (by positivity : 0 ≤ Cutoffs.frontierGradientBound+1)
    have htotal : (r*(Cutoffs.frontierGradientBound+1))*(W.τ*W.c*W.K) ≤
        1*(W.τ*W.c*W.K) := by nlinarith only [hm,hsC]
    exact (mul_le_mul_right (by positivity : 0 < W.τ*W.c*W.K)).mp htotal
  have hr1 : r ≤ 1 := by nlinarith
  have hsquare : (r*(Cutoffs.frontierGradientBound+1))^2 ≤ 1 := by
    nlinarith [mul_nonneg hr (by positivity : 0 ≤ Cutoffs.frontierGradientBound+1)]
  have haux : Cutoffs.frontierGradientBound ≤ (Cutoffs.frontierGradientBound+1)^2 := by nlinarith
  have hbound := mul_le_mul_of_nonneg_left haux (sq_nonneg r)
  change |r| * (1/4) ≤ 1/4 ∧ 2*r^2*(1/4)^2*Cutoffs.frontierGradientBound ≤ 1/4
  rw [abs_of_nonneg hr]
  constructor <;> nlinarith

end WidthConstants
end Smoothness2601.HardProfiles
