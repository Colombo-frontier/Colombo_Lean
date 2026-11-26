import Smoothness2601.HardInstance
import Smoothness2601.SineEntire
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-! Actual joint smoothness, lower-variable analyticity, and entire extensions
of the hard family, with no shared quantitative high-derivative envelope. -/
noncomputable section
open Bilevel.PrimitiveGeometry
open scoped ContDiff
namespace Smoothness2601.Population
variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  {b : Budgets} (P : Population (X := X) (Y := Y) b)

def JointlySmooth : Prop := ContDiff ℝ ∞ P.f ∧ ContDiff ℝ ∞ P.g

def LowerAnalytic : Prop := ∀ x y, AnalyticAt ℝ (fun v => P.f (pack x v)) y ∧
  AnalyticAt ℝ (fun v => P.g (pack x v)) y

end Smoothness2601.Population

namespace Smoothness2601.SineGeometry

theorem lowerObjective_analytic (m a h B y : ℝ) :
    AnalyticAt ℝ (SineLift.lowerObjective m a h B) y := by
  have ha := ((lowerComplex_entire m a h B).analyticAt (y:ℂ)).re_ofReal
  have he : (fun t : ℝ => (lowerComplex m a h B (t:ℂ)).re) = SineLift.lowerObjective m a h B := by
    funext t
    rw [lowerComplex_real]
    rfl
  rwa [he] at ha

theorem upperObjective_analytic (A c y : ℝ) : AnalyticAt ℝ (fun t => A+c*t) y := by
  have ha := ((upperComplex_entire A c).analyticAt (y:ℂ)).re_ofReal
  have he : (fun t : ℝ => (upperComplex A c (t:ℂ)).re) = fun t => A+c*t := by
    funext t
    rw [upperComplex_real]
    rfl
  rwa [he] at ha

namespace Profiles
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  (F : Profiles X) {b : Budgets} (S : F.Calibration b)

theorem population_lowerAnalytic : (F.population S).LowerAnalytic := by
  intro x y
  exact ⟨upperObjective_analytic (F.A x) S.c y,
    lowerObjective_analytic S.m S.a S.h (F.B x) y⟩

theorem population_entire (x : X) : ∃ Fg Gg : ℂ → ℂ,
    Differentiable ℂ Fg ∧ Differentiable ℂ Gg ∧
    (∀ y : ℝ, Fg y = ((F.population S).f (pack x y):ℂ)) ∧
    (∀ y : ℝ, Gg y = ((F.population S).g (pack x y):ℂ)) :=
  ⟨upperComplex (F.A x) S.c,lowerComplex S.m S.a S.h (F.B x),
    upperComplex_entire _ _,lowerComplex_entire _ _ _ _,
    fun y => upperComplex_real _ _ y,fun y => lowerComplex_real _ _ _ _ y⟩

theorem population_jointlySmooth (hA : ContDiff ℝ ∞ F.A) (hB : ContDiff ℝ ∞ F.B) :
    (F.population S).JointlySmooth := by
  have hfst : ContDiff ℝ ∞ (fun z : Joint X ℝ => z.fst) := (first (X := X)).contDiff
  have hsnd : ContDiff ℝ ∞ (fun z : Joint X ℝ => z.snd) := (second (X := X)).contDiff
  have hsin : ContDiff ℝ ∞ Real.sin := Real.contDiff_sin
  have hdiv : ContDiff ℝ ∞ (fun z : Joint X ℝ => z.snd/S.h) := hsnd.div_const S.h
  constructor
  · change ContDiff ℝ ∞ (fun z : Joint X ℝ => F.A z.fst+S.c*z.snd)
    fun_prop
  · change ContDiff ℝ ∞ (fun z : Joint X ℝ =>
      S.m/2*z.snd^2-S.m*S.a*S.h*F.B z.fst*Real.sin (z.snd/S.h))
    fun_prop

end Profiles
end Smoothness2601.SineGeometry

namespace Smoothness2601.HardProfiles
open SineGeometry ExtensiveChain
variable {b : Budgets} {M Λ β : ℝ} (W : WidthConstants b M Λ β)
  {p : WithTop ℕ} (hp : 1 ≤ p) (hβ : 0 ≤ β) {s : ℝ} (hs : 0 < s) (hsδ : s ≤ W.threshold)
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {n : ℕ} (U : Space n →ₗᵢ[ℝ] E)

theorem jointlySmooth : (population W hp hβ hs hsδ U).JointlySmooth := by
  have hA : ContDiff ℝ ∞ (profiles U).A := contDiff_infty.mpr
    (fun k => wrappedA_contDiff radiusConstant chainAmplitude U k)
  have hB : ContDiff ℝ ∞ (profiles U).B := contDiff_infty.mpr
    (fun k => wrappedB_contDiff radiusConstant U k)
  apply ((profiles U).sourceScaled W.τ_pos hs).population_jointlySmooth
  · change ContDiff ℝ ∞ (fun x => (s^2/W.τ)*(profiles U).A ((s/W.τ)⁻¹ • x))
    fun_prop
  · change ContDiff ℝ ∞ (fun x => (profiles U).B ((s/W.τ)⁻¹ • x))
    fun_prop

theorem lowerAnalytic : (population W hp hβ hs hsδ U).LowerAnalytic :=
  ((profiles U).sourceScaled W.τ_pos hs).population_lowerAnalytic (calibration W hp hβ hs hsδ U)

theorem entire (x : E) : ∃ Fg Gg : ℂ → ℂ,
    Differentiable ℂ Fg ∧ Differentiable ℂ Gg ∧
    (∀ y : ℝ, Fg y = ((population W hp hβ hs hsδ U).f (pack x y):ℂ)) ∧
    (∀ y : ℝ, Gg y = ((population W hp hβ hs hsδ U).g (pack x y):ℂ)) :=
  ((profiles U).sourceScaled W.τ_pos hs).population_entire (calibration W hp hβ hs hsδ U) x

end Smoothness2601.HardProfiles
