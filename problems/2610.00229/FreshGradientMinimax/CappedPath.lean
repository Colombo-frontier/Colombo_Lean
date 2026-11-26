import FreshGradientMinimax.FramedPath
import FreshGradientMinimax.RadialCapSmooth
import FreshGradientMinimax.ConvexGradient

/-! The explicit capped signed-path energy, with all global analytic properties
derived from its formula. Constants are uniform in dimension and in the frame. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {n : ℕ}

def cappedPathEnergy (V : Euclid n →ₗᵢ[ℝ] E) (s : Fin (n + 1) → ℝ) (β δ R : ℝ) : E → ℝ :=
  radialCap (framedPathEnergy V s β δ) β R

def cappedPathGradient (V : Euclid n →ₗᵢ[ℝ] E) (s : Fin (n + 1) → ℝ) (β δ R : ℝ) : E → E :=
  radialCapGradient (framedPathEnergy V s β δ) (framedPathGradient V s β δ) β R

theorem cappedPathEnergy_hasFDerivAt (V : Euclid n →ₗᵢ[ℝ] E) (s : Fin (n + 1) → ℝ)
    {β δ R : ℝ} (hβ : 0 < β) (hδ : 0 ≤ δ) (hR : 0 < R) (y : E) :
    HasFDerivAt (cappedPathEnergy V s β δ R) (innerSL ℝ (cappedPathGradient V s β δ R y)) y :=
  radialCap_hasFDerivAt hβ hR (framedPathEnergy_hasFDerivAt V s β hδ) y

theorem cappedPathEnergy_convex (V : Euclid n →ₗᵢ[ℝ] E) (s : Fin (n + 1) → ℝ)
    {β δ R : ℝ} (hβ : 0 < β) (hδ : 0 ≤ δ) (hR : 0 < R) :
    ConvexOn ℝ Set.univ (cappedPathEnergy V s β δ R) :=
  radialCap_convex hβ hR (linearFlatEnergy_convex _ hβ.le hδ)

theorem cappedPathGradient_lipschitz (V : Euclid n →ₗᵢ[ℝ] E)
    {s : Fin (n + 1) → ℝ} (hs : ∀ i, |s i| ≤ 1)
    {β δ R : ℝ} (hβ : 0 < β) (hδ : 0 ≤ δ) (hR : 0 < R) :
    LipschitzWith ⟨1000 * β, by positivity⟩ (cappedPathGradient V s β δ R) := by
  apply radialCapGradient_lipschitz hβ hR (framedPathEnergy_hasFDerivAt V s β hδ)
  · intro x y
    simpa only [dist_eq_norm, NNReal.coe_mk] using
      (framedPathGradient_lipschitz V hs hβ.le hδ).dist_le_mul x y
  · exact framedPathGradient_norm V hs hβ.le hδ
  · exact fun x => (framedPathEnergy_bounds V hs hβ.le hδ x).2

theorem cappedPathEnergy_core (V : Euclid n →ₗᵢ[ℝ] E) (s : Fin (n + 1) → ℝ)
    {β δ R : ℝ} (hβ : 0 ≤ β) (hδ : 0 ≤ δ) {y : E} (hy : ‖y‖ ≤ R) :
    cappedPathEnergy V s β δ R y = framedPathEnergy V s β δ y :=
  radialCap_core hβ (linearFlatEnergy_nonneg _ hβ hδ) hy

theorem cappedPathGradient_core (V : Euclid n →ₗᵢ[ℝ] E) (s : Fin (n + 1) → ℝ)
    {β δ R : ℝ} (hβ : 0 ≤ β) (hδ : 0 ≤ δ) {y : E} (hy : ‖y‖ ≤ R) :
    cappedPathGradient V s β δ R y = framedPathGradient V s β δ y :=
  radialCapGradient_core hβ (linearFlatEnergy_nonneg _ hβ hδ) hy

theorem cappedPathGradient_zero (V : Euclid n →ₗᵢ[ℝ] E) (s : Fin (n + 1) → ℝ)
    {β δ R : ℝ} (hβ : 0 ≤ β) (hδ : 0 ≤ δ) (hR : 0 ≤ R) :
    cappedPathGradient V s β δ R 0 = 0 := by
  rw [cappedPathGradient_core V s hβ hδ (by simpa using hR)]
  exact linearFlatGradient_zero _ β hδ

theorem cappedPathEnergy_outside (V : Euclid n →ₗᵢ[ℝ] E)
    {s : Fin (n + 1) → ℝ} (hs : ∀ i, |s i| ≤ 1)
    {β δ R : ℝ} (hβ : 0 < β) (hδ : 0 ≤ δ) (hR : 0 < R) {y : E} (hy : 2 * R ≤ ‖y‖) :
    cappedPathEnergy V s β δ R y = radialWall β R y - β * R ^ 2 / 2 :=
  radialCap_outside hβ hR (fun x => (framedPathEnergy_bounds V hs hβ.le hδ x).2) hy

theorem cappedPathGradient_outside (V : Euclid n →ₗᵢ[ℝ] E)
    {s : Fin (n + 1) → ℝ} (hs : ∀ i, |s i| ≤ 1)
    {β δ R : ℝ} (hβ : 0 < β) (hδ : 0 ≤ δ) (hR : 0 < R) {y : E} (hy : 2 * R ≤ ‖y‖) :
    cappedPathGradient V s β δ R y = (8 * β) • y :=
  radialCapGradient_outside hβ hR (fun x => (framedPathEnergy_bounds V hs hβ.le hδ x).2) hy

end FreshGradientMinimax
