import Smoothness2601.HardParameters
import Smoothness2601.SineScaledBounds
import Smoothness2601.SineOracle

/-! A fully constructed scalar-inner hard family, with fixed constants before
the order cap and dimension. The probabilistic minimax argument is separate. -/
noncomputable section
open Bilevel.PrimitiveGeometry
namespace Smoothness2601.HardProfiles
open SineGeometry ExtensiveChain
variable {b : Budgets} {M Λ β : ℝ} (W : WidthConstants b M Λ β)
  {p : WithTop ℕ} (hp : 1 ≤ p) (hβ : 0 ≤ β) {s : ℝ} (hs : 0 < s) (hsδ : s ≤ W.threshold)
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {n : ℕ} (U : Space n →ₗᵢ[ℝ] E)

def calibration : ((profiles U).sourceScaled W.τ_pos hs).Calibration b := by
  have hs1 := (W.threshold_conditions hsδ).2.1
  have hh := sineWidth_pos hp hβ W.K_pos hs hs1
  have hbounds := sineWidth_bounds hp hβ hs hs1 W.K_pos
  have hbase := W.baselineThreshold_spec.2.2
    s (sineWidth p β s W.K) hs (W.threshold_conditions hsδ).1 hh hbounds.1 hbounds.2
  exact (profiles U).sourceCalibration W.m_pos.le W.c_pos W.τ_pos hs hh W.c_le W.upper
    hbase.1 hbase.2.1 hbase.2.2.1 hbase.2.2.2

def population : Population (X := E) (Y := ℝ) b :=
  ((profiles U).sourceScaled W.τ_pos hs).population (calibration W hp hβ hs hsδ U)

theorem calibration_amplitude :
    (calibration W hp hβ hs hsδ U).c*(calibration W hp hβ hs hsδ U).a = s^2/W.τ := by
  change W.c*(s^2/(W.τ*W.c)) = s^2/W.τ
  have := W.c_pos.ne'
  field_simp [W.c_pos.ne',W.τ_pos.ne']
  all_goals ring

theorem regularity (hM : 0 < M) (hΛ : 0 < Λ) :
    (population W hp hβ hs hsδ U).HigherRegularity p (derivativeEnvelope b M Λ β) := by
  apply ((profiles U).sourceScaled W.τ_pos hs).population_higherRegularity
  · intro j
    unfold derivativeEnvelope
    split_ifs
    · exact b.L₂_pos.le
    · positivity
  · intro k hk hkp
    rw [derivativeEnvelope,if_neg (by omega : ¬k+1 ≤ 2)]
    exact (profiles U).source_uniform_envelope hp W.m_pos.le W.c_pos W.τ_pos hs
      (W.threshold_conditions hsδ).2.1 W.K_pos hM hΛ hβ W.envelope_ratio W.envelope_scale
      (W.threshold_conditions hsδ).2.2.1 hk hkp

theorem zero_inner : (population W hp hβ hs hsδ U).yStar 0 = 0 := by
  apply ((profiles U).sourceScaled W.τ_pos hs).population_zero_inner
  simpa [Profiles.sourceScaled,Profiles.scaled] using profiles_B_zero U

theorem initialized
    (hgap : (s^2/W.τ)*(gapConstant*(n+1)+1/2) ≤ b.Δ) :
    (population W hp hβ hs hsδ U).Initialized 0 0 := by
  apply (profiles U).source_initialized W.τ_pos hs (calibration W hp hβ hs hsδ U)
    (calibration_amplitude W hp hβ hs hsδ U) (profiles_B_zero U) (profiles_gap U)
  convert hgap using 1
  norm_num [profiles]

theorem gradient_barrier (x : E)
    (hhidden : ∃ j : Fin (n+1),
      |frameProjection U (Bilevel.RadialWrapper.compress (chainRadius radiusConstant n)
        ((s/W.τ)⁻¹ • x)) j| < 1) :
    s/4 ≤ ‖gradient (population W hp hβ hs hsδ U).objective x‖ := by
  have hs1 := (W.threshold_conditions hsδ).2.1
  have hh := sineWidth_pos hp hβ W.K_pos hs hs1
  have hl := (sineWidth_bounds hp hβ hs hs1 W.K_pos).1
  obtain ⟨hsmall,hdist⟩ := W.theta_small hs hsδ hh hl
  exact (profiles U).source_gradient_barrier W.τ_pos hs (calibration W hp hβ hs hsδ U)
    (calibration_amplitude W hp hβ hs hsδ U) hsmall hdist x (profiles_barrier U _ hhidden)

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def oracle : Adaptive.Oracle (population W hp hβ hs hsδ U) Unit := by
  have hs1 := (W.threshold_conditions hsδ).2.1
  have hh := sineWidth_pos hp hβ W.K_pos hs hs1
  have hbounds := sineWidth_bounds hp hβ hs hs1 W.K_pos
  exact ((profiles U).sourceScaled W.τ_pos hs).oracle (calibration W hp hβ hs hsδ U)
    (B := W.signalConstant*s*sineWidth p β s W.K)
    (mul_pos (mul_pos W.signalConstant_pos hs) hh) (W.signal_small hs hsδ hbounds.2)
    ((profiles U).source_signal_bound W.m_pos.le W.c_pos W.τ_pos hs hh W.K_pos hbounds.1)

end Smoothness2601.HardProfiles
