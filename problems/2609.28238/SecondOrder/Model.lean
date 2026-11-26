import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic

open MeasureTheory
open scoped InnerProductSpace

namespace SecondOrder
noncomputable section

abbrev Point (d : ℕ) := EuclideanSpace ℝ (Fin d)

def hessian {d : ℕ} (f : Point d → ℝ) (x : Point d) : Point d →L[ℝ] Point d :=
  fderiv ℝ (gradient f) x

/-- Rayleigh-quotient form of the paper's Hessian condition. -/
def IsSOSP {d : ℕ} (f : Point d → ℝ) (ε γ : ℝ) (x : Point d) : Prop :=
  ‖gradient f x‖ ≤ ε ∧ ∀ v : Point d, -γ*‖v‖^2 ≤ ⟪hessian f x v,v⟫_ℝ

structure Parameters where
  gap : ℝ
  gradientLip : ℝ
  hessianHolder : ℝ
  gradientNoise : ℝ
  hessianNoise : ℝ
  hessianBound : ℝ
  gap_pos : 0 < gap
  gradientLip_pos : 0 < gradientLip
  hessianHolder_pos : 0 < hessianHolder
  gradientNoise_pos : 0 < gradientNoise
  hessianNoise_pos : 0 < hessianNoise
  hessianBound_pos : 0 < hessianBound

/-- The common scalar loss assumptions, retaining the common probability-one
set for the global Hessian error bound. No optimization conclusion is a field. -/
structure CommonLoss {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Parameters) (ν : ℝ)
    (F : Point d → ℝ) (f : Ω → Point d → ℝ) : Prop where
  nu_pos : 0 < ν
  nu_le_one : ν ≤ 1
  population_smooth : ContDiff ℝ 2 F
  gap_bound : ∀ x, F 0-F x ≤ P.gap
  gradient_lipschitz : ∀ x y, ‖gradient F x-gradient F y‖ ≤ P.gradientLip*‖x-y‖
  hessian_holder : ∀ x y, ‖hessian F x-hessian F y‖ ≤ P.hessianHolder*‖x-y‖^ν
  value_measurable : Measurable (fun zx : Ω × Point d => f zx.1 zx.2)
  gradient_measurable : Measurable (fun zx : Ω × Point d => gradient (f zx.1) zx.2)
  hessian_measurable : Measurable (fun zx : Ω × Point d => hessian (f zx.1) zx.2)
  sample_regularity : ∀ᵐ z ∂μ, ContDiff ℝ 2 (f z) ∧ ∃ C : ℝ, 0 ≤ C ∧
    ∀ x y, ‖hessian (f z) x-hessian (f z) y‖ ≤ C*‖x-y‖
  value_integrable : ∀ x, Integrable (fun z => f z x) μ
  gradient_integrable : ∀ x, Integrable (fun z => gradient (f z) x) μ
  hessian_integrable : ∀ x, Integrable (fun z => hessian (f z) x) μ
  value_unbiased : ∀ x, (∫ z, f z x ∂μ) = F x
  gradient_unbiased : ∀ x, (∫ z, gradient (f z) x ∂μ) = gradient F x
  hessian_unbiased : ∀ x, (∫ z, hessian (f z) x ∂μ) = hessian F x
  gradient_error_integrable : ∀ x, Integrable (fun z => ‖gradient (f z) x-gradient F x‖^2) μ
  gradient_variance : ∀ x, (∫ z, ‖gradient (f z) x-gradient F x‖^2 ∂μ) ≤ P.gradientNoise^2
  hvp_error_integrable : ∀ x v, Integrable (fun z => ‖(hessian (f z) x-hessian F x) v‖^2) μ
  hvp_variance : ∀ x v, (∫ z, ‖(hessian (f z) x-hessian F x) v‖^2 ∂μ) ≤
    P.hessianNoise^2*‖v‖^2
  global_hessian_bound : ∀ᵐ z ∂μ, ∀ x, ‖hessian (f z) x-hessian F x‖ ≤ P.hessianBound

structure RichCommonLoss {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Parameters) (σ₀ : ℝ)
    (F : Point d → ℝ) (f : Ω → Point d → ℝ) : Prop extends CommonLoss μ P 1 F f where
  valueNoise_pos : 0 < σ₀
  value_error_integrable : ∀ x, Integrable (fun z => |f z x-F x|^2) μ
  value_variance : ∀ x, (∫ z, |f z x-F x|^2 ∂μ) ≤ σ₀^2

abbrev RichReply (d : ℕ) := ℝ × Point d × (Point d →L[ℝ] Point d)

def richReply {Ω : Type*} {d : ℕ} (f : Ω → Point d → ℝ) (z : Ω) (x : Point d) : RichReply d :=
  (f z x, gradient (f z) x, hessian (f z) x)

inductive HvpQuery (d : ℕ)
  | grad : Point d → HvpQuery d
  | hvp : Point d → Point d → HvpQuery d

def queryPoint {d : ℕ} : HvpQuery d → Point d
  | .grad x => x
  | .hvp x _ => x

def extractHvp {d : ℕ} (q : HvpQuery d) (r : RichReply d) : Point d :=
  match q with
  | .grad _ => r.2.1
  | .hvp _ v => r.2.2 v

def hvpReply {Ω : Type*} {d : ℕ} (f : Ω → Point d → ℝ) (z : Ω) : HvpQuery d → Point d
  | .grad x => gradient (f z) x
  | .hvp x v => hessian (f z) x v

theorem one_rich_call_simulates_hvp {Ω : Type*} {d : ℕ}
    (f : Ω → Point d → ℝ) (z : Ω) (q : HvpQuery d) :
    extractHvp q (richReply f z (queryPoint q)) = hvpReply f z q := by cases q <;> rfl

theorem gap_implies_bounded_below {d : ℕ} {F : Point d → ℝ} {Δ : ℝ}
    (hgap : ∀ x, F 0-F x ≤ Δ) : BddBelow (Set.range F) := by
  refine ⟨F 0-Δ, ?_⟩
  rintro _ ⟨x,rfl⟩
  linarith [hgap x]

theorem certificate_yields_sosp {d : ℕ} {F : Point d → ℝ} {g x : Point d}
    {ε γ : ℝ} (hε : 0 ≤ ε) (hsmall : ‖g‖ ≤ 4*(ε/10))
    (haccurate : ‖g-gradient F x‖ ≤ (ε/10)/2)
    (hcert : ∀ v, -γ*‖v‖^2 ≤ ⟪hessian F x v,v⟫_ℝ) : IsSOSP F ε γ x := by
  refine ⟨?_,hcert⟩
  have h := norm_add_le (gradient F x-g) g
  rw [sub_add_cancel, norm_sub_rev (gradient F x) g] at h
  linarith

end
end SecondOrder
