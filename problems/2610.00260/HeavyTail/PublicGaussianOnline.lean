import HeavyTail.ChangingGaussianOnline
import HeavyTail.MixtureFiniteNet

/-! One public finite net covers every fixed comparator in the decision
ball. It is chosen solely from the center, radius and round budget, before
the predictable means or conditional noise kernels are supplied. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Classical InnerProductSpace

namespace HeavyTail.GaussianEntropy
open GaussianEstimates AdaptiveKernel
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

structure GaussianOnlineNet (E : Type u) [NormedAddCommGroup E] (c : E) (R ρ : ℝ) where
  points : Set E
  finite_points : points.Finite
  center_mem : c ∈ points
  in_ball : ∀ z ∈ points, ‖z - c‖ ≤ R
  cover : ∀ u, ‖u - c‖ ≤ R → ∃ z ∈ points, ‖z - u‖ ≤ ρ

abbrev GaussianOnlineNet.Index {c : E} {R ρ : ℝ} (N : GaussianOnlineNet E c R ρ) := N.points

instance GaussianOnlineNet.indexFintype {c : E} {R ρ : ℝ} (N : GaussianOnlineNet E c R ρ) :
    Fintype N.Index := N.finite_points.fintype

instance GaussianOnlineNet.indexNonempty {c : E} {R ρ : ℝ} (N : GaussianOnlineNet E c R ρ) :
    Nonempty N.Index := ⟨⟨c, N.center_mem⟩⟩

def GaussianOnlineNet.centers {c : E} {R ρ : ℝ} (N : GaussianOnlineNet E c R ρ) : N.Index → E :=
  Subtype.val

def GaussianOnlineNet.centerIndex {c : E} {R ρ : ℝ} (N : GaussianOnlineNet E c R ρ) : N.Index :=
  ⟨c, N.center_mem⟩

theorem gaussianOnlineNet_nonempty (c : E) {R ρ : ℝ} (hR : 0 ≤ R) (hρ : 0 < ρ) :
    Nonempty (GaussianOnlineNet E c R ρ) := by
  obtain ⟨Z, hZ, hc, hb, hcover⟩ := finite_ball_comparator_net c hR hρ
  refine ⟨⟨Z, hZ, hc, ?_, ?_⟩⟩
  · intro z hz
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hb hz
  · intro u hu
    obtain ⟨z, hz, hnear⟩ := hcover u (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hu)
    exact ⟨z, hz, by simpa only [norm_sub_rev] using hnear.le⟩

def publicOnlineNet (c : E) {R : ℝ} {n : ℕ} (hR : 0 < R) (hn : 0 < n) :
    GaussianOnlineNet E c R (R / (8 * n)) :=
  Classical.choice (gaussianOnlineNet_nonempty c hR.le (div_pos hR
    (mul_pos (by norm_num) (Nat.cast_pos.mpr hn))))

theorem conditional_mixed_moment_online_rate {Seed : Type u} [MeasurableSpace Seed] {n : ℕ}
    (κ : (t : ℕ) → Kernel (History Seed E t) E) [∀ t, IsMarkovKernel (κ t)]
    (P : Measure Seed) [IsProbabilityMeasure P]
    (b : (t : ℕ) → History Seed E t → E) {p s V M R α : ℝ}
    (hbm : ∀ t, Measurable (b t)) (hbb : ∀ t h, ‖b t h‖ ≤ M)
    (h2 : ∀ t h, Integrable (fun r => ‖r - b t h‖ ^ 2) (κ t h))
    (hzero : ∀ t h, (∫ r, r - b t h ∂κ t h) = 0)
    (hsecond : ∀ t h, (∫ r, ‖r - b t h‖ ^ 2 ∂κ t h) ≤ V)
    (hweak : ∀ t h v, ‖v‖ = 1 → (∫ r, |⟪v, r - b t h⟫_ℝ| ^ p ∂κ t h) ≤ s ^ p)
    (hp : 1 < p) (hp2 : p ≤ 2) (hM : 0 < M) (hV : 0 ≤ V) (hs : 0 < s)
    (c : E) (hR : 0 < R) (hα : 0 < α) (hα1 : α < 1 / 10) (hn : 0 < n)
    (u : E) (hu : ‖u - c‖ ≤ R) :
    let N := publicOnlineNet c hR hn
    (changingHistoryLaw P κ n).real {h |
      (96 + 16 * mixedConstant p) * R * ((M + Real.sqrt V) / Real.sqrt n +
        M * confidenceLog α / n + s * (confidenceLog α / n) ^ (1 - 1 / p)) <
      historySum (predictableGaussianRegret N.centers
        (tunedGaussianWeights c (p := p) hM hV hs hR hα hα1 hn N.centers N.centerIndex) b u) n h / n} ≤ α := by
  let N := publicOnlineNet c hR hn
  have hb : ∀ i : N.Index, ‖N.centers i - c‖ ≤ R := fun i => N.in_ball i i.property
  have hnear : ∃ i : N.Index, ‖N.centers i - u‖ ≤ R / (8 * n) := by
    obtain ⟨z, hz, hdist⟩ := N.cover u hu
    exact ⟨⟨z, hz⟩, hdist⟩
  exact changingKernel_online_rate κ P b hbm hbb h2 hzero hsecond hweak hp hp2 hM hV hs
    c hR hα hα1 hn N.centers hb N.centerIndex rfl u hnear

end HeavyTail.GaussianEntropy
