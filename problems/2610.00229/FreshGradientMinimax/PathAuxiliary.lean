import FreshGradientMinimax.PathTruncation
import FreshGradientMinimax.PathCanonical
import FreshGradientMinimax.PathOutside

/-! The sign-independent auxiliary response, with exact agreement at each good
query of an unrestricted algorithm. Outside the cap it uses the radial formula;
inside it uses the newly exposed coordinates and the full ambient norm. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace

def truncatedPathOperator {n dy : ℕ} (C : Euclid dy →L[ℝ] Euclid n) (w : ℕ) :
    Euclid dy →L[ℝ] Euclid (n + 1) :=
  (pathIncidence (fun _ => 1)).comp ((coordinateMask (pathVisible n w)).comp C)

def auxiliaryPathCapGradient {n dy : ℕ} (C : Euclid dy →L[ℝ] Euclid n)
    (β δ R : ℝ) (w : ℕ) (y : Euclid dy) : Euclid dy :=
  if 2 * R < ‖y‖ then (8 * β) • y else
    radialCapGradient (linearFlatEnergy (truncatedPathOperator C w) β δ)
      (linearFlatGradient (truncatedPathOperator C w) β δ) β R y

theorem cappedPathGradient_auxiliary {N t dy : ℕ} (ht : t < N)
    (V : Euclid (4 * N + 4) →ₗᵢ[ℝ] Euclid dy) {s β δ R : ℝ}
    (hs : s ^ 2 = 1) (hβ : 0 < β) (hδ : 0 ≤ δ) (hR : 0 < R) (y : Euclid dy)
    (hgood : ‖y‖ ≤ 2 * R → ∀ i ∉ pathVisible (4 * N + 4) (t + 1),
      |frameCoordinates V y i| ≤ δ / 2) :
    cappedPathGradient V (pathSignsFromVertices (tailVertexSigns (2 * N + 2) s)) β δ R y =
      auxiliaryPathCapGradient (frameCoordinates V) β δ R (t + 2) y := by
  unfold auxiliaryPathCapGradient
  split_ifs with hy
  · exact cappedPathGradient_outside V (pathSignsFromVertices_abs (tailVertexSigns_sq _ hs))
      hβ hδ hR hy.le
  · have hsmall := hgood (le_of_not_gt hy)
    unfold cappedPathGradient framedPathEnergy framedPathGradient framedPathOperator
    rw [linearFlatEnergy_gauge_central (frameCoordinates V) _ hs hδ β,
      linearFlatGradient_gauge_central (frameCoordinates V) _ hs hδ β]
    rw [path_bands_cap_gradient (n := 4 * N + 3) (frameCoordinates V) (by omega : 0 < t + 1)
      (centralPathSigns_abs _ hs) hδ hsmall β R]
    rw [centralPath_bands_sign_independent (by omega : t + 1 ≤ N)]
    rfl

def pathAuxiliaryReply (p : Parameters) (N : ℕ) {dy : ℕ}
    (C : Euclid dy →L[ℝ] Euclid (4 * N + 4)) (u v : Euclid dy) (t : ℕ)
    (z : Joint 1 dy) : Joint 1 dy :=
  (realVector (penaltySaddleGradX (p.L / 4) (p.L / 8) (4 * p.ε) u (realCoord z.1) z.2),
    penaltySaddleGradY
      (auxiliaryPathCapGradient C (p.L / 8192) (pathHardFlatWidth p.L p.μ p.ε (4 * N + 3))
        (pathHardRadius p.L p.μ p.ε (4 * N + 3)) (t + 2))
      (p.L / 8) p.μ (pathHardSignal p.L p.μ p.ε (4 * N + 3)) u v (realCoord z.1) z.2)

theorem pathHorizon_reply_auxiliary (p : Parameters) (hκ : 4 * p.μ ≤ p.L)
    {N t dy : ℕ} (ht : t < N) (V : Euclid (4 * N + 4) →ₗᵢ[ℝ] Euclid dy)
    {s : ℝ} (hs : s ^ 2 = 1) (z : Joint 1 dy)
    (hgood : ‖z.2‖ ≤ 2 * pathHardRadius p.L p.μ p.ε (4 * N + 3) →
      ∀ i ∉ pathVisible (4 * N + 4) (t + 1),
        |frameCoordinates V z.2 i| ≤ pathHardFlatWidth p.L p.μ p.ε (4 * N + 3) / 2) :
    (pathHorizonObjective p hκ N V s hs).jointGradient z =
      pathAuxiliaryReply p N (frameCoordinates V) (V (EuclideanSpace.single 0 1))
        (V (EuclideanSpace.single (Fin.last (4 * N + 3)) 1)) t z := by
  have hL : 0 < p.L := by linarith [p.μ_pos]
  apply Prod.ext
  · rfl
  · change (p.L / 8 * realCoord z.1) • V (EuclideanSpace.single 0 1) - p.μ • z.2 -
      cappedPathGradient V (pathSignsFromVertices (tailVertexSigns (2 * N + 2) s))
        (p.L / 8192) (pathHardFlatWidth p.L p.μ p.ε (4 * N + 3))
        (pathHardRadius p.L p.μ p.ε (4 * N + 3)) z.2 + _ = _
    rw [cappedPathGradient_auxiliary ht V hs (by positivity : 0 < p.L / 8192)
      (pathHardFlatWidth_pos hL p.μ_pos p.ε_pos _).le
      (pathHardRadius_pos hL p.μ_pos p.ε_pos _) z.2 hgood]
    rfl

end FreshGradientMinimax
