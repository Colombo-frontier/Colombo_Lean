import FreshGradientMinimax.PrimalRawAuxiliary
import FreshGradientMinimax.CoinPrefixCount
import FreshGradientMinimax.CoordinateFrame

/-! A single independent raw label array supplies both frame blocks. The
unstopped run and its final output do not read any unrevealed label. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace FreshGradientMinimax

def primalLabelStage (n : ℕ) : Fin ((n + 1) + (n + n)) → ℕ :=
  Fin.addCases (fun i => i.val) (Fin.addCases (fun e => e.val + 1) (fun e => e.val + 1))

def primalLabels {n D : ℕ} (z : Fin ((n + 1) + (n + n)) → Fin D) : Fin (n + 1) → Fin D :=
  fun i => z (i.castAdd (n + n))

def dualLabels {n D : ℕ} (z : Fin ((n + 1) + (n + n)) → Fin D) : Fin (n + n) → Fin D :=
  fun i => z (i.natAdd (n + 1))

theorem primalLabels_injective {n D : ℕ} {z : Fin ((n + 1) + (n + n)) → Fin D}
    (hz : Function.Injective z) : Function.Injective (primalLabels z) := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun a : Fin ((n + 1) + (n + n)) => a.val) (hz h)

theorem dualLabels_injective {n D : ℕ} {z : Fin ((n + 1) + (n + n)) → Fin D}
    (hz : Function.Injective z) : Function.Injective (dualLabels z) := by
  intro i j h
  apply Fin.ext
  have he := congrArg Fin.val (hz h)
  change n + 1 + i.val = n + 1 + j.val at he
  omega

theorem primalLabel_prefix_congr {n D j : ℕ} {z z' : Fin ((n + 1) + (n + n)) → Fin D}
    (h : ∀ i, primalLabelStage n i < j → z i = z' i) :
    primalPrefixRead j (coordinateRead (primalLabels z)) = primalPrefixRead j (coordinateRead (primalLabels z')) ∧
    dualPrefixRead j (coordinateRead (dualLabels z)) = dualPrefixRead j (coordinateRead (dualLabels z')) := by
  constructor
  · apply primalPrefixRead_congr
    intro i hi x
    change x (z (i.castAdd (n + n))) = x (z' (i.castAdd (n + n)))
    rw [h _ (by simpa only [primalLabelStage, Fin.addCases_left] using hi)]
  · apply dualPrefixRead_congr
    intro e he y
    constructor
    · change y (z ((e.castAdd n).natAdd (n + 1))) = y (z' ((e.castAdd n).natAdd (n + 1)))
      rw [h _ (by simpa only [primalLabelStage, Fin.addCases_right, Fin.addCases_left] using he)]
    · change y (z ((e.natAdd n).natAdd (n + 1))) = y (z' ((e.natAdd n).natAdd (n + 1)))
      rw [h _ (by simpa only [primalLabelStage, Fin.addCases_right] using he)]

def primalLabelReply {n D : ℕ} (z : Fin ((n + 1) + (n + n)) → Fin D)
    (L ε μ σ : ℝ) (c : ℕ → Bool) (t : ℕ) : Joint D D → Joint D D :=
  primalRawAuxiliaryReply (coordinateRead (primalLabels z)) (coordinateRead (dualLabels z))
    L ε μ σ (coinPrefixCount c t) (c t)

theorem primalLabelReply_measurable {n D : ℕ} (z : Fin ((n + 1) + (n + n)) → Fin D)
    {L ε μ : ℝ} (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ) (σ : ℝ) (c : ℕ → Bool) (t : ℕ) :
    Measurable (primalLabelReply z L ε μ σ c t) :=
  primalRawAuxiliaryReply_measurable _ _ hL hε hμ σ _ _

theorem primalLabelReply_congr {n D : ℕ} {z z' : Fin ((n + 1) + (n + n)) → Fin D}
    {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε) (μ σ : ℝ) (c : ℕ → Bool) (t : ℕ)
    (h : ∀ i, primalLabelStage n i ≤ coinPrefixCount c (t + 1) → z i = z' i) :
    primalLabelReply z L ε μ σ c t = primalLabelReply z' L ε μ σ c t := by
  apply rawAuxiliaryReply_congr _ _ _ _ (primalLengthScale_pos hL hε).le
  · apply (primalLabel_prefix_congr (j := coinPrefixCount c t + 1 + if c t then 1 else 0) ?_).1
    intro i hi
    apply h i
    rw [coinPrefixCount_succ]
    omega
  · apply (primalLabel_prefix_congr (j := coinPrefixCount c t + 1 + if c t then 1 else 0) ?_).2
    intro i hi
    apply h i
    rw [coinPrefixCount_succ]
    omega

namespace Algorithm
variable {n D : ℕ} {Seed : Type*} [MeasurableSpace Seed] (A : Algorithm D D Seed)

def primalLabelQuery (z : Fin ((n + 1) + (n + n)) → Fin D) (L ε μ σ : ℝ)
    (c : ℕ → Bool) (t : ℕ) (seed : Seed) : Joint D D :=
  A.query t (A.deterministicRun (primalLabelReply z L ε μ σ c) t seed)

def primalLabelOutput (z : Fin ((n + 1) + (n + n)) → Fin D) (L ε μ σ : ℝ)
    (c : ℕ → Bool) (N : ℕ) (seed : Seed) : Euclid D :=
  A.output N (A.deterministicRun (primalLabelReply z L ε μ σ c) N seed)

theorem primalLabelRun_congr {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε) (μ σ : ℝ)
    (c : ℕ → Bool) (seed : Seed) (t : ℕ) {z z' : Fin ((n + 1) + (n + n)) → Fin D}
    (h : ∀ i, primalLabelStage n i ≤ coinPrefixCount c t → z i = z' i) :
    A.deterministicRun (primalLabelReply z L ε μ σ c) t seed =
      A.deterministicRun (primalLabelReply z' L ε μ σ c) t seed := by
  refine A.first_exit_transcript_identity _ _ seed t ?_ t le_rfl
  intro s hs
  apply congrFun (primalLabelReply_congr hL hε μ σ c s ?_)
  intro i hi
  exact h i (hi.trans (coinPrefixCount_monotone c (by omega)))

theorem primalLabelQuery_update_hidden {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε) (μ σ : ℝ)
    (c : ℕ → Bool) (seed : Seed) (t : ℕ) (z : Fin ((n + 1) + (n + n)) → Fin D)
    (i : Fin ((n + 1) + (n + n))) (hi : coinPrefixCount c t < primalLabelStage n i) (j : Fin D) :
    A.primalLabelQuery (Function.update z i j) L ε μ σ c t seed = A.primalLabelQuery z L ε μ σ c t seed := by
  unfold primalLabelQuery
  rw [A.primalLabelRun_congr hL hε μ σ c seed t]
  intro k hk
  have hki : k ≠ i := by intro he; subst k; omega
  exact Function.update_of_ne hki j z

theorem primalLabelOutput_update_hidden {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε) (μ σ : ℝ)
    (c : ℕ → Bool) (seed : Seed) (N : ℕ) (z : Fin ((n + 1) + (n + n)) → Fin D)
    (i : Fin ((n + 1) + (n + n))) (hi : coinPrefixCount c N < primalLabelStage n i) (j : Fin D) :
    A.primalLabelOutput (Function.update z i j) L ε μ σ c N seed = A.primalLabelOutput z L ε μ σ c N seed := by
  unfold primalLabelOutput
  rw [A.primalLabelRun_congr hL hε μ σ c seed N]
  intro k hk
  have hki : k ≠ i := by intro he; subst k; omega
  exact Function.update_of_ne hki j z

theorem primalLabelQuery_measurable (z : Fin ((n + 1) + (n + n)) → Fin D)
    {L ε μ : ℝ} (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ) (σ : ℝ) (c : ℕ → Bool) (t : ℕ) :
    Measurable (A.primalLabelQuery z L ε μ σ c t) :=
  (A.query_measurable t).comp (A.deterministicRun_measurable _ (primalLabelReply_measurable z hL hε hμ σ c) t)

theorem primalLabelOutput_measurable (z : Fin ((n + 1) + (n + n)) → Fin D)
    {L ε μ : ℝ} (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ) (σ : ℝ) (c : ℕ → Bool) (N : ℕ) :
    Measurable (A.primalLabelOutput z L ε μ σ c N) :=
  (A.output_measurable N).comp (A.deterministicRun_measurable _ (primalLabelReply_measurable z hL hε hμ σ c) N)

end Algorithm
end FreshGradientMinimax
