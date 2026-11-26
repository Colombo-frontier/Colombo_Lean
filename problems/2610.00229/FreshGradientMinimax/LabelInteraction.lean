import FreshGradientMinimax.AuxiliaryMeasurable
import FreshGradientMinimax.CoordinateFrame
import FreshGradientMinimax.Transcript

/-! The actual unstopped auxiliary interaction on a finite raw label list.
Its t-th query depends only on the two bands exposed before that query. The
collision fallback is used only for the hard objective, not for this process. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace FreshGradientMinimax

def labelAuxiliaryReply (p : Parameters) (N : ℕ) {D : ℕ} (z : Fin (4 * N + 4) → Fin D) :
    ℕ → Joint 1 D → Joint 1 D :=
  pathAuxiliaryReply p N (coordinateRead z) (EuclideanSpace.single (z 0) 1)
    (EuclideanSpace.single (z (Fin.last (4 * N + 3))) 1)

theorem labelAuxiliaryReply_measurable (p : Parameters) (N : ℕ) {D : ℕ}
    (z : Fin (4 * N + 4) → Fin D) (t : ℕ) : Measurable (labelAuxiliaryReply p N z t) :=
  pathAuxiliaryReply_measurable p N _ _ _ t

theorem labelAuxiliaryReply_congr (p : Parameters) (N : ℕ) {D : ℕ}
    {z z' : Fin (4 * N + 4) → Fin D} (t : ℕ)
    (h : ∀ i ∈ pathVisible (4 * N + 4) (t + 2), z i = z' i) :
    labelAuxiliaryReply p N z t = labelAuxiliaryReply p N z' t := by
  have hfirst := h 0 (pathVisible_first (by omega))
  have hlast := h (Fin.last (4 * N + 3)) (pathVisible_last (by omega))
  unfold labelAuxiliaryReply
  rw [hfirst, hlast]
  apply pathAuxiliaryReply_congr
  intro i hi y
  change y (z i) = y (z' i)
  rw [h i hi]

namespace Algorithm
variable {D : ℕ} {Seed : Type*} [MeasurableSpace Seed] (A : Algorithm 1 D Seed)

def labelQuery (p : Parameters) (N : ℕ) (z : Fin (4 * N + 4) → Fin D) (t : ℕ)
    (seed : Seed) : Joint 1 D :=
  A.query t (A.deterministicRun (labelAuxiliaryReply p N z) t seed)

theorem labelRun_congr (p : Parameters) (N : ℕ) (seed : Seed) (t : ℕ)
    {z z' : Fin (4 * N + 4) → Fin D}
    (h : ∀ i ∈ pathVisible (4 * N + 4) (t + 1), z i = z' i) :
    A.deterministicRun (labelAuxiliaryReply p N z) t seed =
      A.deterministicRun (labelAuxiliaryReply p N z') t seed := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hold : ∀ i ∈ pathVisible (4 * N + 4) (t + 1), z i = z' i :=
      fun i hi => h i (pathVisible_mono (by omega) hi)
    simp only [deterministicRun, deterministicStep]
    rw [ih hold, labelAuxiliaryReply_congr p N t h]

theorem labelQuery_congr (p : Parameters) (N : ℕ) (seed : Seed) (t : ℕ)
    {z z' : Fin (4 * N + 4) → Fin D}
    (h : ∀ i ∈ pathVisible (4 * N + 4) (t + 1), z i = z' i) :
    A.labelQuery p N z t seed = A.labelQuery p N z' t seed := by
  unfold labelQuery
  rw [A.labelRun_congr p N seed t h]

theorem labelQuery_update_hidden (p : Parameters) (N : ℕ) (seed : Seed) (t : ℕ)
    (z : Fin (4 * N + 4) → Fin D) (i : Fin (4 * N + 4))
    (hi : i ∉ pathVisible (4 * N + 4) (t + 1)) (j : Fin D) :
    A.labelQuery p N (Function.update z i j) t seed = A.labelQuery p N z t seed := by
  apply A.labelQuery_congr
  intro k hk
  have hki : k ≠ i := by intro he; subst k; exact hi hk
  simp only [Function.update_of_ne hki]

theorem labelQuery_measurable (p : Parameters) (N : ℕ) (z : Fin (4 * N + 4) → Fin D) (t : ℕ) :
    Measurable (A.labelQuery p N z t) :=
  (A.query_measurable t).comp
    (A.deterministicRun_measurable (labelAuxiliaryReply p N z) (labelAuxiliaryReply_measurable p N z) t)

end Algorithm

theorem labelFrame_reply_auxiliary (p : Parameters) (hκ : 4 * p.μ ≤ p.L)
    {N t D : ℕ} (ht : t < N) (hD : 4 * N + 4 ≤ D) (z : Fin (4 * N + 4) → Fin D)
    (hz : Function.Injective z) {s : ℝ} (hs : s ^ 2 = 1) (q : Joint 1 D)
    (hgood : ‖q.2‖ ≤ 2 * pathHardRadius p.L p.μ p.ε (4 * N + 3) →
      ∀ i ∉ pathVisible (4 * N + 4) (t + 1),
        |q.2 (z i)| ≤ pathHardFlatWidth p.L p.μ p.ε (4 * N + 3) / 2) :
    (pathHorizonObjective p hκ N (labelFrame hD z) s hs).jointGradient q =
      labelAuxiliaryReply p N z t q := by
  rw [labelFrame_of_injective hD z hz]
  have hg : ‖q.2‖ ≤ 2 * pathHardRadius p.L p.μ p.ε (4 * N + 3) →
      ∀ i ∉ pathVisible (4 * N + 4) (t + 1),
        |frameCoordinates (coordinateFrame z hz) q.2 i| ≤
          pathHardFlatWidth p.L p.μ p.ε (4 * N + 3) / 2 := by
    simpa only [coordinateFrame_coordinates, coordinateRead_apply] using hgood
  rw [pathHorizon_reply_auxiliary p hκ ht (coordinateFrame z hz) hs q hg,
    coordinateFrame_coordinates, coordinateFrame_single, coordinateFrame_single]
  rfl

namespace Algorithm
variable {D : ℕ} {Seed : Type*} [MeasurableSpace Seed] (A : Algorithm 1 D Seed)

def LabelGood (p : Parameters) (N : ℕ) (z : Fin (4 * N + 4) → Fin D) (seed : Seed) : Prop :=
  Function.Injective z ∧ ∀ t < N,
    ‖(A.labelQuery p N z t seed).2‖ ≤ 2 * pathHardRadius p.L p.μ p.ε (4 * N + 3) →
      ∀ i ∉ pathVisible (4 * N + 4) (t + 1),
        |(A.labelQuery p N z t seed).2 (z i)| ≤ pathHardFlatWidth p.L p.μ p.ε (4 * N + 3) / 2

theorem labelGood_output_identity (p : Parameters) (hκ : 4 * p.μ ≤ p.L) (N : ℕ)
    (hD : 4 * N + 4 ≤ D) (z : Fin (4 * N + 4) → Fin D) (seed : Seed)
    {s : ℝ} (hs : s ^ 2 = 1) (hg : A.LabelGood p N z seed) :
    A.output N (A.deterministicRun
      (fun _ => (pathHorizonObjective p hκ N (labelFrame hD z) s hs).jointGradient) N seed) =
      A.output N (A.deterministicRun (labelAuxiliaryReply p N z) N seed) := by
  apply A.first_exit_output_identity
  intro t ht
  exact labelFrame_reply_auxiliary p hκ ht hD z hg.1 hs (A.labelQuery p N z t seed) (hg.2 t ht)

end Algorithm
end FreshGradientMinimax
