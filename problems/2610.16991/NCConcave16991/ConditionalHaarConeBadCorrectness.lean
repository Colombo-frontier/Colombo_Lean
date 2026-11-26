import NCConcave16991.ConditionalHaarConeBadEvent
import NCConcave16991.ConeReferenceGoodness

/-! # The concrete observable cone Bad event contains every successful output -/

open Set MeasureTheory
open scoped InnerProductSpace

namespace NCConcave16991.Haar.ConeMachine

noncomputable section

set_option maxHeartbeats 1000000
attribute [local irreducible] runWithRows observedSupport

variable (k n M : ℕ) (R : ℝ) (hR : 0 < R)
  {Ω : Type*} [MeasurableSpace Ω]
  (P : OraclePolicy.AdaptivePolicy (Domain (FrameSpace k) M R hR) (n := n)
    (dx := ConeProblem.primalDimension (FrameSpace k) M) Ω)

/-- The finite three-probe enumeration covers exactly the no-leak conditions
used by the deterministic actual-oracle coupling. -/
theorem not_badEvent_noLeak (seed : Ω) (hn : 0 < n) (q : ℝ) (e : Fin n ↪ Fin k)
    (Q : Fin (M + 1) → OrthogonalGroup k) (T : ℕ)
    (hgood : (seed,Q) ∉ badEvent k n M R hR P hn q e T) : NoLeak k n M R hR P seed hn q e Q T := by
  intro t ht j i hi
  let τ : Fin (T + 1) := ⟨t, by omega⟩
  have hkind (b : Fin 3) :
      |⟪finiteProbe k n M R hR P hn T j (probeEncoding n T (b,τ,i)) seed
        (boundary (FrameSpace k) n M R hR P seed hn q (frameRows k n M e Q) t),
        frameRows k n M e Q j i⟫_ℝ| < leakRadius n := by
    by_contra h
    apply hgood
    change (seed,Q) ∈ allStageBad k n M R hR P hn q e (probeTime n T)
      (finiteProbe k n M R hR P hn T) (probeRow n T) (leakRadius n)
    apply Set.mem_iUnion.mpr
    refine ⟨j, ?_⟩
    change ∃ a : Fin (probeCount n T),
      e (probeRow n T a) ∉ observedSupport k n M R hR P seed hn q (frameRows k n M e Q) e j (probeTime n T a) ∧
      leakRadius n ≤ |⟪finiteProbe k n M R hR P hn T j a seed
        (runWithRows (FrameSpace k) n M R hR P seed hn q (frameRows k n M e Q) (probeTime n T a)),
        orthogonalLinearIsometryEquiv (Q j) (basisVector (e (probeRow n T a)))⟫_ℝ|
    refine ⟨probeEncoding n T (b,τ,i), ?_, ?_⟩
    · simpa only [probeTime_encoded, probeRow_encoded] using hi
    · have hh := le_of_not_gt h
      simpa only [probeTime_encoded, probeRow_encoded, boundary, frameRows] using hh
  have h0 := (hkind (0 : Fin 3)).le
  have h1 := (hkind (1 : Fin 3)).le
  have h2 := (hkind (2 : Fin 3)).le
  constructor
  · simpa [finiteProbe, leakRadius] using h0
  constructor
  · simpa [finiteProbe, leakRadius] using h1
  · simpa [finiteProbe, leakRadius] using h2

def actualProblem (hn : 0 < n) (q : ℝ) (hq : 16 ≤ q) (e : Fin n ↪ Fin k)
    (Q : Fin (M + 1) → OrthogonalGroup k) :=
  ConeProblem.problem hn ConeSmooth.individualConstant ConeSmooth.individualConstant_pos R hR q (by linarith)
    (fun i j ↦ frameRows k n M e Q j i) (frameRows_orthonormal k n M e Q)

/-- This is pointwise in the static Haar-family problem. No joint
measurability of the Moreau stationarity predicate is needed. -/
theorem stationary_implies_badEvent (seed : Ω) (hn : 0 < n) (q : ℝ)
    (hR1 : 1 ≤ R) (hq : 16 ≤ q) (hrel : Real.sqrt (n : ℝ) = q * R)
    (hq2 : Real.sqrt (n : ℝ) ≤ q ^ 2) (e : Fin n ↪ Fin k)
    (Q : Fin (M + 1) → OrthogonalGroup k) (T : ℕ)
    (hbudget : (T : ℝ) < (n : ℝ) * (M + 1 : ℕ) / 4096)
    (hstat : StationaryOutput (actualProblem k n M R hR hn q hq e Q)
      (OraclePolicy.run (Domain (FrameSpace k) M R hR) P
        (oracleResponse (actualProblem k n M R hR hn q hq e Q)) seed T).1) :
    (seed,Q) ∈ badEvent k n M R hR P hn q e T := by
  by_contra h
  exact noLeak_not_stationary k n M R hR P seed hn q hR1 hq hrel hq2 e Q T hbudget
    (not_badEvent_noLeak k n M R hR P seed hn q e Q T h) hstat

end

end NCConcave16991.Haar.ConeMachine
