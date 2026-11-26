import FullJet.EpochPath
import FullJet.FiniteDescent

open scoped BigOperators

namespace FullJet

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {p n B m : ℕ}

noncomputable def epochBoundaryCount (hp : 1 ≤ p) (f : Fin n → E → ℝ) (center : E)
    (M r : ℝ) (hr : 0 ≤ r) (samples : Fin m → Fin B → Fin n) : ℝ :=
  finiteBoundaryCount (epochPathStep hp f center M r hr samples) r

theorem epochBoundaryCount_nonneg (hp : 1 ≤ p) (f : Fin n → E → ℝ) (center : E)
    (M r : ℝ) (hr : 0 ≤ r) (samples : Fin m → Fin B → Fin n) :
    0 ≤ epochBoundaryCount hp f center M r hr samples := finiteBoundaryCount_nonneg _ _

/-- Sum the actual noisy model descents before taking expectations. The endpoint
term is retained so that it telescopes across later snapshot resets. -/
theorem Admissible.epoch_boundary_budget {f : Fin n → E → ℝ} {Δ L : ℝ}
    (hf : Admissible p n Δ L f) (hp : 1 ≤ p) (hL : 0 ≤ L) (hm : 0 < m)
    (center : E) (M r : ℝ) (hr : 0 ≤ r) (hA : 0 ≤ M / ((p + 1).factorial : ℝ) - L)
    (samples : Fin m → Fin B → Fin n) :
    (M / ((p + 1).factorial : ℝ) - L) * r ^ (p + 1) *
      epochBoundaryCount hp f center M r hr samples ≤
      average f center - average f (epochPathPoint hp f center M r hr samples (Fin.last m)) +
      r * ∑ t, epochPathError hp f center M r hr samples t +
      (m : ℝ) * ((p : ℝ) * L * (m : ℝ) ^ (p - 1)) * r ^ (p + 1) := by
  have h := finite_boundary_descent_budget
    (fun t => average f (epochPathPoint hp f center M r hr samples t))
    (epochPathStep hp f center M r hr samples) (epochPathError hp f center M r hr samples)
    r (M / ((p + 1).factorial : ℝ) - L) ((p : ℝ) * L * (m : ℝ) ^ (p - 1)) hA p
    (hf.epochPath_descent hp hL hm center M r hr samples)
  simpa only [epochBoundaryCount, epochPathPoint_zero] using h

theorem epochPathError_mean_sum_le [Nonempty (Fin n)] {f : Fin n → E → ℝ} {k : ℕ}
    (hf : ∀ i, ContDiff ℝ (k + 2) (f i)) (hB : 0 < B) (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ i a b, ‖iteratedFDeriv ℝ (k + 2) (f i) a -
      iteratedFDeriv ℝ (k + 2) (f i) b‖ ≤ L * ‖a - b‖)
    (center : E) (M r : ℝ) (hr : 0 ≤ r) :
    uniformMean (fun samples : Fin m → Fin B → Fin n =>
      ∑ t, epochPathError (p := k + 2) (by omega) f center M r hr samples t) ≤
        (m : ℝ) * epochNoiseBound (k + 2) L m r B := by
  rw [uniformMean_sum]
  calc
    _ ≤ ∑ _t : Fin m, epochNoiseBound (k + 2) L m r B :=
      Finset.sum_le_sum (fun t _ => epochPathError_mean_le hf hB L hL hlip center M r hr t)
    _ = _ := by simp

end FullJet
