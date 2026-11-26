import FreshGradientMinimax.CorePrefixDependence
import FreshGradientMinimax.PartialGradientRegularity
import FreshGradientMinimax.PrimalTruncation

/-! Truncated scalar models on arbitrary linear reads. Prefixing the reads
preserves the actual scalar objective and makes hidden-coordinate independence explicit. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace

def linearCoreInteraction {n dy : ℕ} (B : Euclid dy →L[ℝ] Euclid (n + n))
    (a R : ℝ) (j : ℕ) (u : Euclid (n + 1)) (y : Euclid dy) : ℝ :=
  a * weightedCoreLinks (coordinateMultiplier (coreLinkPrefix n j) (clipVector R (B y))) u

def linearTruncatedCore {n dy : ℕ} (B : Euclid dy →L[ℝ] Euclid (n + n))
    (μ t : ℝ) (j : ℕ) (u : Euclid (n + 1)) (y : Euclid dy) : ℝ :=
  (μ * t ^ 2) * weightedCoreSeed (coreSeedPrefix n j) u - μ / 2 * ‖y‖ ^ 2 -
    smoothMaximum (coreCapHeight n μ t)
      (μ / 2 * ‖y‖ ^ 2 - linearCoreInteraction B (2 * μ * t) (32 * t) j u y)
      (coreProtectedWall n μ t y)

def linearCompressedCoordinates {m dx : ℕ} (A : Euclid dx →L[ℝ] Euclid m)
    (r R : ℝ) (x : Euclid dx) : Euclid m := r⁻¹ • A (radialCompression R x)

def rawCompressedObjective {n dx dy : ℕ} (A : Euclid dx →L[ℝ] Euclid (n + 1))
    (B : Euclid dy →L[ℝ] Euclid (n + n)) (r R β μ t : ℝ) (j : ℕ) (x : Euclid dx) (y : Euclid dy) : ℝ :=
  linearTruncatedCore B μ t j (linearCompressedCoordinates A r R x) y + β / 2 * ‖x‖ ^ 2

def rawTruncatedObjective {n dx dy : ℕ} (A : Euclid dx →L[ℝ] Euclid (n + 1))
    (B : Euclid dy →L[ℝ] Euclid (n + n)) (r R β μ t : ℝ) (j : ℕ) :=
  rawCompressedObjective (primalPrefixRead j A) (dualPrefixRead j B) r R β μ t j

def rawTruncatedGradient {n dx dy : ℕ} (A : Euclid dx →L[ℝ] Euclid (n + 1))
    (B : Euclid dy →L[ℝ] Euclid (n + n)) (r R β μ t : ℝ) (j : ℕ) : Joint dx dy → Joint dx dy :=
  actualJointGradient (rawTruncatedObjective A B r R β μ t j)

theorem linearTruncatedCore_prefix_read {n dy j : ℕ} (B : Euclid dy →L[ℝ] Euclid (n + n))
    (μ t : ℝ) (hj : 0 < j) (u : Euclid (n + 1)) (y : Euclid dy) :
    linearTruncatedCore (dualPrefixRead j B) μ t j (corePrimalPrefix j u) y =
      linearTruncatedCore B μ t j u y := by
  unfold linearTruncatedCore linearCoreInteraction dualPrefixRead
  rw [ContinuousLinearMap.comp_apply, clipVector_prefix_read, coreSeed_prefix_read hj,
    weightedCoreLinks_prefix_congr _ _ u (corePrimalPrefix_known u)]

theorem rawTruncatedObjective_eq {n dx dy j : ℕ} (A : Euclid dx →L[ℝ] Euclid (n + 1))
    (B : Euclid dy →L[ℝ] Euclid (n + n)) (r R β μ t : ℝ) (hj : 0 < j) :
    rawTruncatedObjective A B r R β μ t j = rawCompressedObjective A B r R β μ t j := by
  funext x y
  unfold rawTruncatedObjective rawCompressedObjective
  have he : linearCompressedCoordinates (primalPrefixRead j A) r R x =
      corePrimalPrefix j (linearCompressedCoordinates A r R x) := by
    simp only [linearCompressedCoordinates, primalPrefixRead, ContinuousLinearMap.comp_apply, map_smul]
  rw [he, linearTruncatedCore_prefix_read B μ t hj]

theorem rawTruncatedObjective_frame {n dx dy j : ℕ} (U : Euclid (n + 1) →ₗᵢ[ℝ] Euclid dx)
    (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy) (r R β μ t : ℝ) (hj : 0 < j) :
    rawTruncatedObjective (frameCoordinates U) (frameCoordinates V) r R β μ t j =
      compressedObjective U (truncatedCoreObjective V μ t j) r R β := by
  rw [rawTruncatedObjective_eq _ _ r R β μ t hj]
  rfl

theorem linearCompressedCoordinates_contDiff {m dx : ℕ} (A : Euclid dx →L[ℝ] Euclid m)
    (r R : ℝ) {k : ℕ∞} : ContDiff ℝ k (linearCompressedCoordinates A r R) :=
  (A.contDiff.comp (radialCompression_contDiff R)).const_smul r⁻¹

theorem linearTruncatedCore_contDiff {n dy : ℕ} (B : Euclid dy →L[ℝ] Euclid (n + n))
    {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) (j : ℕ) :
    ContDiff ℝ 1 (fun z : Euclid (n + 1) × Euclid dy => linearTruncatedCore B μ t j z.1 z.2) := by
  have hn : ContDiff ℝ 1 (fun z : Euclid (n + 1) × Euclid dy => ‖z.2‖ ^ 2) :=
    (contDiff_norm_sq ℝ).comp contDiff_snd
  have hc : ContDiff ℝ 1 (fun z : Euclid (n + 1) × Euclid dy =>
      coordinateMultiplier (coreLinkPrefix n j) (clipVector (32 * t) (B z.2))) :=
    (coordinateMultiplier _).contDiff.comp (((clipVector_contDiff _).of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).comp
      (B.contDiff.comp contDiff_snd))
  have hΓ : ContDiff ℝ 1 (fun z : Euclid (n + 1) × Euclid dy => linearCoreInteraction B (2 * μ * t) (32 * t) j z.1 z.2) :=
    contDiff_const.mul (hc.inner ℝ (coreLinks_contDiff.comp contDiff_fst))
  have hW : ContDiff ℝ 1 (fun z : Euclid (n + 1) × Euclid dy => coreProtectedWall n μ t z.2) :=
    (contDiff_const.mul hn).sub contDiff_const
  have hK : ContDiff ℝ 1 (fun z : Euclid (n + 1) × Euclid dy =>
      smoothMaximum (coreCapHeight n μ t)
        (μ / 2 * ‖z.2‖ ^ 2 - linearCoreInteraction B (2 * μ * t) (32 * t) j z.1 z.2)
        (coreProtectedWall n μ t z.2)) := (smoothMaximum_contDiff (coreCapHeight_pos n hμ ht)).comp
    (((contDiff_const.mul hn).sub hΓ).prodMk hW)
  exact ((contDiff_const.mul ((weightedCoreSeed_contDiff _).comp contDiff_fst)).sub (contDiff_const.mul hn)).sub hK

theorem rawTruncatedObjective_contDiff {n dx dy : ℕ} (A : Euclid dx →L[ℝ] Euclid (n + 1))
    (B : Euclid dy →L[ℝ] Euclid (n + n)) (r R β : ℝ) {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) (j : ℕ) :
    ContDiff ℝ 1 (fun z : Joint dx dy => rawTruncatedObjective A B r R β μ t j z.1 z.2) :=
  ((linearTruncatedCore_contDiff _ hμ ht j).comp
    (((linearCompressedCoordinates_contDiff _ r R).comp contDiff_fst).prodMk contDiff_snd)).add
      (contDiff_const.mul ((contDiff_norm_sq ℝ).comp contDiff_fst))

theorem rawTruncatedGradient_continuous {n dx dy : ℕ} (A : Euclid dx →L[ℝ] Euclid (n + 1))
    (B : Euclid dy →L[ℝ] Euclid (n + n)) (r R β : ℝ) {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) (j : ℕ) :
    Continuous (rawTruncatedGradient A B r R β μ t j) :=
  actualJointGradient_continuous (rawTruncatedObjective_contDiff A B r R β hμ ht j)

theorem rawTruncatedGradient_congr {n dx dy j : ℕ}
    (A A' : Euclid dx →L[ℝ] Euclid (n + 1)) (B B' : Euclid dy →L[ℝ] Euclid (n + n))
    (r R β μ t : ℝ) (hA : primalPrefixRead j A = primalPrefixRead j A')
    (hB : dualPrefixRead j B = dualPrefixRead j B') :
    rawTruncatedGradient A B r R β μ t j = rawTruncatedGradient A' B' r R β μ t j := by
  unfold rawTruncatedGradient rawTruncatedObjective
  rw [hA, hB]

theorem rawTruncatedGradient_paper {n dx dy j : ℕ} (U : Euclid (n + 1) →ₗᵢ[ℝ] Euclid dx)
    (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy) {L ε μ : ℝ} (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ)
    (hm : μ ≤ L / (4 * primalScalingConstant)) (hj : 0 < j) :
    rawTruncatedGradient (frameCoordinates U) (frameCoordinates V) (primalLengthScale L ε)
      (primalCompressionRadius n L ε) (primalRidgeCoefficient L ε) μ (Real.sqrt (primalValueScale L ε / μ)) j =
      (paperTruncatedModel U V hL hε hμ hm j).jointGradient := by
  unfold rawTruncatedGradient
  rw [rawTruncatedObjective_frame _ _ _ _ _ _ _ hj]
  exact actualJointGradient_objective (paperTruncatedModel U V hL hε hμ hm j)

end FreshGradientMinimax
