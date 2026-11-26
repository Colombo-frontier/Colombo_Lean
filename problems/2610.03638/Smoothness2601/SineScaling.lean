import Smoothness2601.ScaledProfiles
import Smoothness2601.UniformCalibration

/-! Source amplitude s²/τ and spatial scale s/τ, including the actual
baseline Population inequalities with an order-uniform accuracy threshold. -/
noncomputable section
namespace Smoothness2601.SineGeometry.Profiles
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  (F : Profiles X)

def sourceScaled {τ s : ℝ} (hτ : 0 < τ) (hs : 0 < s) : Profiles X :=
  F.scaled (amp := s^2/τ) (scale := s/τ) (by positivity) (by positivity)

theorem sourceScaled_constants {τ s : ℝ} (hτ : 0 < τ) (hs : 0 < s) :
    (F.sourceScaled hτ hs).LA = τ*F.LA ∧
    (F.sourceScaled hτ hs).C₀ = F.C₀ ∧
    (F.sourceScaled hτ hs).C₁ = τ*F.C₁/s ∧
    (F.sourceScaled hτ hs).C₂ = τ^2*F.C₂/s^2 := by
  dsimp [sourceScaled,scaled]
  constructor
  · field_simp; ring
  constructor
  · rfl
  constructor <;> field_simp <;> ring

def sourceCalibration {b : Budgets} {m c τ s h : ℝ}
    (hm : 0 ≤ m) (hc : 0 < c) (hτ : 0 < τ) (hs : 0 < s) (hh : 0 < h)
    (hcL : c ≤ b.L₀) (hLA : τ*F.LA ≤ b.L₁)
    (hstrong : b.μ ≤ m-(m/c)*(s^2/(τ*h))*F.C₀)
    (hsmooth : m+(m/c)*(τ*h*F.C₂+2*s*F.C₁+(s^2/(τ*h))*F.C₀) ≤ b.L₁)
    (hmixed : (m/c)*(τ*F.C₂+(s/h)*F.C₁) ≤ b.L₂)
    (hlower : (m/c)*((s/h)*F.C₁+(s^2/(τ*h^2))*F.C₀) ≤ b.L₂) :
    (F.sourceScaled hτ hs).Calibration b where
  m := m
  a := s^2/(τ*c)
  h := h
  c := c
  m_nonneg := hm
  a_nonneg := by positivity
  h_pos := hh
  upper_y := by rwa [abs_of_pos hc]
  upper_smooth := by rwa [(F.sourceScaled_constants hτ hs).1]
  strong := by
    rw [(F.sourceScaled_constants hτ hs).2.1]
    convert hstrong using 1
    field_simp
    ring
  lower_smooth := by
    unfold signalLipschitz
    rw [(F.sourceScaled_constants hτ hs).2.2.1,(F.sourceScaled_constants hτ hs).2.2.2,
      (F.sourceScaled_constants hτ hs).2.1]
    convert hsmooth using 1
    field_simp
    ring
  mixed_lipschitz := by
    rw [(F.sourceScaled_constants hτ hs).2.2.1,(F.sourceScaled_constants hτ hs).2.2.2]
    convert hmixed using 1
    field_simp
    ring
  lower_lipschitz := by
    rw [(F.sourceScaled_constants hτ hs).2.2.1,(F.sourceScaled_constants hτ hs).2.1]
    convert hlower using 1
    field_simp
    ring

end Smoothness2601.SineGeometry.Profiles

namespace Smoothness2601

theorem exists_baseline_threshold {b : Budgets} {m c τ K C₀ C₁ C₂ : ℝ}
    (hmμ : b.μ < m) (hmL : m < b.L₁) (hc : 0 < c) (hτ : 0 < τ) (hK : 0 < K)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hxx : (m/c)*τ*K*C₂ ≤ (b.L₁-m)/2)
    (hxy : (m/c)*(τ*C₂+C₁/K) ≤ b.L₂)
    (hyy : (m/c)*(C₁/K+C₀/(τ*K^2)) ≤ b.L₂) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ s h : ℝ, 0 < s → s ≤ δ → 0 < h → K*s ≤ h → h ≤ K →
      b.μ ≤ m-(m/c)*(s^2/(τ*h))*C₀ ∧
      m+(m/c)*(τ*h*C₂+2*s*C₁+(s^2/(τ*h))*C₀) ≤ b.L₁ ∧
      (m/c)*(τ*C₂+(s/h)*C₁) ≤ b.L₂ ∧
      (m/c)*((s/h)*C₁+(s^2/(τ*h^2))*C₀) ≤ b.L₂ := by
  have hm : 0 < m := b.μ_pos.trans hmμ
  have hmc : 0 < m/c := div_pos hm hc
  let D := (m/c)*C₀/(τ*K)
  let G := 2*(m/c)*C₁+D
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hG : 0 ≤ G := by dsimp [G]; positivity
  let δ := min 1 (min ((m-b.μ)/(D+1)) ((b.L₁-m)/(2*(G+1))))
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min zero_lt_one (lt_min
      (div_pos (sub_pos.mpr hmμ) (by positivity))
      (div_pos (sub_pos.mpr hmL) (by positivity)))
  refine ⟨δ,hδ,min_le_left _ _,?_⟩
  intro s h hs hsδ hh hl hu
  obtain ⟨hr₁,hr₂,hr₃,hr₄⟩ := width_ratios hτ hK hs hh hl hu
  have hsD : s ≤ (m-b.μ)/(D+1) := hsδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsG : s ≤ (b.L₁-m)/(2*(G+1)) := hsδ.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hstrong : (m/c)*(s^2/(τ*h))*C₀ ≤ s*D := by
    have hh' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr₄ hmc.le) hC₀
    exact hh'.trans_eq (by dsimp [D]; ring)
  have hX : (m/c)*(τ*h*C₂) ≤ (b.L₁-m)/2 := by
    have hh' := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hr₁ hC₂) hmc.le
    exact hh'.trans (by convert hxx using 1; ring)
  refine ⟨?_,?_,?_,?_⟩
  · have hd := (le_div_iff₀ (by positivity : 0 < D+1)).mp hsD
    nlinarith
  · have hg := (le_div_iff₀ (by positivity : 0 < 2*(G+1))).mp hsG
    have he : (m/c)*(τ*h*C₂+2*s*C₁+(s^2/(τ*h))*C₀) =
        (m/c)*(τ*h*C₂)+2*(m/c)*s*C₁+(m/c)*(s^2/(τ*h))*C₀ := by ring
    rw [he]
    dsimp [G] at hg
    nlinarith
  · apply le_trans _ hxy
    apply mul_le_mul_of_nonneg_left _ hmc.le
    exact add_le_add_left ((mul_le_mul_of_nonneg_right hr₂ hC₁).trans_eq (by ring)) _
  · apply le_trans _ hyy
    apply mul_le_mul_of_nonneg_left _ hmc.le
    exact add_le_add
      ((mul_le_mul_of_nonneg_right hr₂ hC₁).trans_eq (by ring))
      ((mul_le_mul_of_nonneg_right hr₃ hC₀).trans_eq (by ring))

end Smoothness2601
