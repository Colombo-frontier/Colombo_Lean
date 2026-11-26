import FreshGradientMinimax.RawStaticIndex
import FreshGradientMinimax.RawExteriorReply

/-! The unstopped auxiliary reply on arbitrary linear reads. A failed coin
uses the current prefix; a successful coin uses at most one further stage. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory

theorem primalPrefixRead_eq_of_le {m d j J : ℕ} (h : j ≤ J)
    {A A' : Euclid d →L[ℝ] Euclid m} (hA : primalPrefixRead J A = primalPrefixRead J A') :
    primalPrefixRead j A = primalPrefixRead j A' := by
  rw [← primalPrefixRead_nested h A, hA, primalPrefixRead_nested h A']

theorem dualPrefixRead_eq_of_le {n d j J : ℕ} (h : j ≤ J)
    {B B' : Euclid d →L[ℝ] Euclid (n + n)} (hB : dualPrefixRead J B = dualPrefixRead J B') :
    dualPrefixRead j B = dualPrefixRead j B' := by
  rw [← dualPrefixRead_nested h B, hB, dualPrefixRead_nested h B']

def rawInteriorBase {n dx dy : ℕ} (A : Euclid dx →L[ℝ] Euclid (n + 1))
    (B : Euclid dy →L[ℝ] Euclid (n + n)) (r R β μ t : ℝ) (k : ℕ) (z : Joint dx dy) : Joint dx dy :=
  rawTruncatedGradient A B r R β μ t ((rawStaticIndex A B r R k z).val + 1) z

def rawAuxiliaryReply {n dx dy : ℕ} (A : Euclid dx →L[ℝ] Euclid (n + 1))
    (B : Euclid dy →L[ℝ] Euclid (n + n)) (r R β μ t p Ry : ℝ) (k : ℕ) (c : Bool)
    (z : Joint dx dy) : Joint dx dy :=
  if ‖z.2‖ < Ry then jointMaskedReply p (rawInteriorBase A B r R β μ t k z)
    (rawTruncatedGradient A B r R β μ t (min (k + 2) (n + 1)) z) c
  else rawExteriorReply A (μ * t ^ 2) r R β μ (k + 1) z

theorem rawInteriorBase_measurable {n dx dy : ℕ} (A : Euclid dx →L[ℝ] Euclid (n + 1))
    (B : Euclid dy →L[ℝ] Euclid (n + n)) (r R β : ℝ) {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) (k : ℕ) :
    Measurable (rawInteriorBase A B r R β μ t k) :=
  measurable_selected_truncation _ (rawStaticIndex_measurable A B r R k)
    (fun i => rawTruncatedGradient A B r R β μ t (i.val + 1))
    (fun i => (rawTruncatedGradient_continuous A B r R β hμ ht (i.val + 1)).measurable)

theorem rawAuxiliaryReply_measurable {n dx dy : ℕ} (A : Euclid dx →L[ℝ] Euclid (n + 1))
    (B : Euclid dy →L[ℝ] Euclid (n + n)) (r R β : ℝ) {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t)
    (p Ry : ℝ) (k : ℕ) (c : Bool) : Measurable (rawAuxiliaryReply A B r R β μ t p Ry k c) := by
  apply Measurable.ite (measurableSet_lt (continuous_snd.norm.measurable) measurable_const)
  · cases c
    · exact rawInteriorBase_measurable A B r R β hμ ht k
    · exact jointMaskedReply_true_measurable _ _ _ (rawInteriorBase_measurable A B r R β hμ ht k)
        (rawTruncatedGradient_continuous A B r R β hμ ht _).measurable
  · exact (rawExteriorReply_continuous A (μ * t ^ 2) r R β μ (k + 1)).measurable

theorem rawInteriorBase_congr {n dx dy k : ℕ}
    (A A' : Euclid dx →L[ℝ] Euclid (n + 1)) (B B' : Euclid dy →L[ℝ] Euclid (n + n))
    {r : ℝ} (hr : 0 ≤ r) (R β μ t : ℝ)
    (hA : primalPrefixRead (k + 1) A = primalPrefixRead (k + 1) A')
    (hB : dualPrefixRead (k + 1) B = dualPrefixRead (k + 1) B') :
    rawInteriorBase A B r R β μ t k = rawInteriorBase A' B' r R β μ t k := by
  funext z
  have he := congrFun (rawStaticIndex_congr A A' B B' r R hA hB) z
  have hj : (rawStaticIndex A' B' r R k z).val + 1 ≤ k + 1 :=
    Nat.add_le_add_right (rawStaticIndex_le A' B' hr R k z) 1
  unfold rawInteriorBase
  rw [he, rawTruncatedGradient_congr A A' B B' r R β μ t
    (primalPrefixRead_eq_of_le hj hA) (dualPrefixRead_eq_of_le hj hB)]

theorem rawAuxiliaryReply_congr {n dx dy k : ℕ}
    (A A' : Euclid dx →L[ℝ] Euclid (n + 1)) (B B' : Euclid dy →L[ℝ] Euclid (n + n))
    {r : ℝ} (hr : 0 ≤ r) (R β μ t p Ry : ℝ) (c : Bool)
    (hA : primalPrefixRead (k + 1 + if c then 1 else 0) A = primalPrefixRead (k + 1 + if c then 1 else 0) A')
    (hB : dualPrefixRead (k + 1 + if c then 1 else 0) B = dualPrefixRead (k + 1 + if c then 1 else 0) B') :
    rawAuxiliaryReply A B r R β μ t p Ry k c = rawAuxiliaryReply A' B' r R β μ t p Ry k c := by
  have hle : k + 1 ≤ k + 1 + if c then 1 else 0 := Nat.le_add_right _ _
  have hA0 := primalPrefixRead_eq_of_le hle hA
  have hB0 := dualPrefixRead_eq_of_le hle hB
  have hb := rawInteriorBase_congr A A' B B' hr R β μ t hA0 hB0
  have he := rawExteriorReply_congr (dy := dy) A A' (μ * t ^ 2) r R β μ hA0
  cases c
  · funext z
    simp only [rawAuxiliaryReply, hb, he, jointMaskedReply, maskedReply, Bool.false_eq_true, if_false]
  · have hn : min (k + 2) (n + 1) ≤ k + 1 + if true then 1 else 0 := by
      simpa only [if_true, Nat.add_assoc] using Nat.min_le_left (k + 2) (n + 1)
    have hf := rawTruncatedGradient_congr A A' B B' r R β μ t
      (primalPrefixRead_eq_of_le hn hA) (dualPrefixRead_eq_of_le hn hB)
    funext z
    simp only [rawAuxiliaryReply, hb, he, hf]

def primalRawAuxiliaryReply {n dx dy : ℕ} (A : Euclid dx →L[ℝ] Euclid (n + 1))
    (B : Euclid dy →L[ℝ] Euclid (n + n)) (L ε μ σ : ℝ) (k : ℕ) (c : Bool) : Joint dx dy → Joint dx dy :=
  rawAuxiliaryReply A B (primalLengthScale L ε) (primalCompressionRadius n L ε)
    (primalRidgeCoefficient L ε) μ (Real.sqrt (primalValueScale L ε / μ))
    (primalRevealProbability L ε μ σ) (paperDualProtectionRadius n μ (primalValueScale L ε)) k c

theorem primalRawAuxiliaryReply_measurable {n dx dy : ℕ} (A : Euclid dx →L[ℝ] Euclid (n + 1))
    (B : Euclid dy →L[ℝ] Euclid (n + n)) {L ε μ : ℝ} (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ)
    (σ : ℝ) (k : ℕ) (c : Bool) : Measurable (primalRawAuxiliaryReply A B L ε μ σ k c) :=
  rawAuxiliaryReply_measurable A B _ _ _ hμ
    (Real.sqrt_pos.mpr (div_pos (primalValueScale_pos hL hε) hμ)) _ _ k c

theorem primalRawAuxiliaryReply_paper {n dx dy : ℕ} (U : Euclid (n + 1) →ₗᵢ[ℝ] Euclid dx)
    (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy) {L ε μ : ℝ} (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ)
    (hm : μ ≤ L / (4 * primalScalingConstant)) (σ : ℝ) (k : Fin (n + 1)) (c : Bool) (z : Joint dx dy)
    (hu : ∀ i : Fin (n + 1), k.val < i.val →
      |compressedCoordinates U (primalLengthScale L ε) (primalCompressionRadius n L ε) z.1 i| ≤ 1 / 4)
    (hy : ‖z.2‖ < paperDualProtectionRadius n μ (primalValueScale L ε) →
      ∀ e : Fin n, k.val ≤ e.val →
        |frameCoordinates V z.2 (e.castAdd n)| ≤ primalLengthScale L ε ∧
        |frameCoordinates V z.2 (e.natAdd n)| ≤ primalLengthScale L ε) :
    primalRawAuxiliaryReply (frameCoordinates U) (frameCoordinates V) L ε μ σ k.val c z =
      primalCoinReply U V hL hε hμ hm σ c z := by
  unfold primalRawAuxiliaryReply rawAuxiliaryReply
  split_ifs with hz
  · have hb : rawInteriorBase (frameCoordinates U) (frameCoordinates V) (primalLengthScale L ε)
        (primalCompressionRadius n L ε) (primalRidgeCoefficient L ε) μ
        (Real.sqrt (primalValueScale L ε / μ)) k.val z = primalStaticBase U V hL hε hμ hm z := by
      unfold rawInteriorBase
      rw [rawStaticIndex_paper U V hL hε k.val z hu (hy hz),
        rawTruncatedGradient_paper U V hL hε hμ hm (Nat.succ_pos _)]
      rfl
    rw [hb, rawTruncatedGradient_paper U V hL hε hμ hm (by omega),
      paperTruncatedModel_next_gradient U V hL hε hμ hm k z hu]
    rfl
  · have he : μ * Real.sqrt (primalValueScale L ε / μ) ^ 2 = primalValueScale L ε := by
      rw [Real.sq_sqrt (div_nonneg (primalValueScale_pos hL hε).le hμ.le)]
      exact mul_div_cancel₀ _ (ne_of_gt hμ)
    rw [he, rawExteriorReply_paper U V hL hε hμ hm (Nat.succ_pos _) z (le_of_not_gt hz)]
    exact (primalCoinReply_exterior U V hL hε hμ hm σ k.val z c hu (le_of_not_gt hz)).symm

end FreshGradientMinimax
