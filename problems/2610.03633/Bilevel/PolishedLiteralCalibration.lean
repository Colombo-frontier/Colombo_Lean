import Bilevel.PolishedLiteralValueBounds
import Bilevel.PolishedLiteralEntry

/-! Compatible numerical choices for the manuscript's actual micro value
budget. The common radius constant and receiver amplitude are fixed before
zeta, and kappa is chosen last. -/
noncomputable section
namespace Bilevel.PolishedLiteral
open ChiBoundedChain

def payloadTolerance (C Cu A ζ κ : ℝ) : ℝ :=
  ZeroChainPotential.phi 0/κ^2+C*Cu*ζ^2+9*A*ζ+3*A/κ

theorem payload_parameters (C Cu A wstar γ : ℝ)
    (hC : 0≤C) (hCu : 0<Cu) (hA : 0<A) (hws : 0<wstar) (hγ : 0<γ) :
    ∃ ζ κ₀ : ℝ,0<ζ ∧ ζ≤1 ∧ ζ≤wstar/20 ∧ 4≤κ₀ ∧ 2/ζ^3≤κ₀ ∧
      ∀ κ : ℝ,κ₀≤κ → 0≤payloadTolerance C Cu A ζ κ ∧ payloadTolerance C Cu A ζ κ≤γ := by
  let B := ZeroChainPotential.phi 0+C*Cu+12*A+1
  have hφ : 0≤ZeroChainPotential.phi 0 := ZeroChainPotential.phi_nonneg _
  have hCC : 0≤C*Cu := mul_nonneg hC hCu.le
  have hB : 0<B := by dsimp [B];positivity
  let ζ := min 1 (min (wstar/20) (γ/(4*B)))
  have hζ : 0<ζ := lt_min zero_lt_one (lt_min (by positivity) (by positivity))
  have hζ1 : ζ≤1 := min_le_left _ _
  have hζw : ζ≤wstar/20 := (min_le_right _ _).trans (min_le_left _ _)
  have hζB : ζ≤γ/(4*B) := (min_le_right _ _).trans (min_le_right _ _)
  let κ₀ := max 4 (max (2/ζ^3) (4*B/γ))
  have hκ₀ : 4≤κ₀ := le_max_left _ _
  have hκscale : 2/ζ^3≤κ₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hκB : 4*B/γ≤κ₀ := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨ζ,κ₀,hζ,hζ1,hζw,hκ₀,hκscale,?_⟩
  intro κ hκ
  have hκ4 : 4≤κ := hκ₀.trans hκ
  have hκpos : 0<κ := by linarith
  have hκ1 : 1≤κ := by linarith
  have ht0 : 0≤1/κ := by positivity
  have ht1 : 1/κ≤1 := (div_le_one hκpos).mpr hκ1
  have htB : 1/κ≤γ/(4*B) := by
    apply (div_le_div_iff₀ hκpos (by positivity : 0<4*B)).mpr
    have hh := (div_le_iff₀ hγ).mp (hκB.trans hκ)
    nlinarith only [hh]
  have hζsq : ζ^2≤ζ := by nlinarith
  have htsq : (1/κ)^2≤1/κ := by nlinarith
  have hbound : payloadTolerance C Cu A ζ κ≤B*ζ+B*(1/κ) := by
    have hs := mul_le_mul_of_nonneg_left hζsq hCC
    have ht := mul_le_mul_of_nonneg_left htsq hφ
    have he : ZeroChainPotential.phi 0/κ^2=ZeroChainPotential.phi 0*(1/κ)^2 := by ring
    unfold payloadTolerance
    rw [he,div_eq_mul_inv]
    dsimp only [B]
    have hcζ : 0≤(ZeroChainPotential.phi 0+3*A+1)*ζ := by positivity
    have hcκ : 0≤(C*Cu+9*A+1)*(1/κ) := by positivity
    simp only [one_div,div_eq_mul_inv] at hs ht hcζ hcκ ⊢
    nlinarith only [hs,ht,hcζ,hcκ]
  have hζsmall := mul_le_mul_of_nonneg_left hζB hB.le
  have htsmall := mul_le_mul_of_nonneg_left htB hB.le
  have hcancel : B*(γ/(4*B))=γ/4 := by field_simp;ring
  rw [hcancel] at hζsmall htsmall
  constructor
  · unfold payloadTolerance
    positivity
  · linarith

end Bilevel.PolishedLiteral
