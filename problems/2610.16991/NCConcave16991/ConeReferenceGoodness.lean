import NCConcave16991.ConeReferenceCoupling
import NCConcave16991.ConditionalHaarConeMachineProbe
import NCConcave16991.ConditionalHaarConeMachineSupport
import NCConcave16991.ConditionalHaarRowMean

/-! # The actual no-leak row event rules out stationary arbitrary policy outputs -/

open Set MeasureTheory
open scoped InnerProductSpace

namespace NCConcave16991.Haar.ConeMachine

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable (k n M : ℕ) (R : ℝ) (hR : 0 < R)
  {Ω : Type*} [MeasurableSpace Ω]
  (P : OraclePolicy.AdaptivePolicy (Domain (FrameSpace k) M R hR) (n := n)
    (dx := ConeProblem.primalDimension (FrameSpace k) M) Ω)

def NoLeak (seed : Ω) (hn : 0 < n) (q : ℝ) (e : Fin n ↪ Fin k)
    (Q : Fin (M + 1) → OrthogonalGroup k) (T : ℕ) : Prop :=
  ∀ t ≤ T, ∀ j : Fin (M + 1), ∀ i : Fin n,
    e i ∉ observedSupport k n M R hR P seed hn q (frameRows k n M e Q) e j ((n + 2) * t) →
      |⟪querySourceProbe (FrameSpace k) n M R hR P seed hn j
        (boundary (FrameSpace k) n M R hR P seed hn q (frameRows k n M e Q) t),
        frameRows k n M e Q j i⟫_ℝ| ≤ 1 / (64 * Real.sqrt (n : ℝ)) ∧
      |⟪queryClockProbe (FrameSpace k) n M R hR P seed hn j
        (boundary (FrameSpace k) n M R hR P seed hn q (frameRows k n M e Q) t),
        frameRows k n M e Q j i⟫_ℝ| ≤ 1 / (64 * Real.sqrt (n : ℝ)) ∧
      |⟪finalSourceProbe (FrameSpace k) n M R hR P seed j
        (boundary (FrameSpace k) n M R hR P seed hn q (frameRows k n M e Q) t),
        frameRows k n M e Q j i⟫_ℝ| ≤ 1 / (64 * Real.sqrt (n : ℝ))

theorem noLeak_source_correlations (seed : Ω) (hn : 0 < n) (q : ℝ) (e : Fin n ↪ Fin k)
    (Q : Fin (M + 1) → OrthogonalGroup k) (T : ℕ)
    (hno : NoLeak k n M R hR P seed hn q e Q T)
    (t : ℕ) (ht : t ≤ T) (j : Fin (M + 1))
    (hj : (boundary (FrameSpace k) n M R hR P seed hn q (frameRows k n M e Q) t).progress.1 ≤ j.val) :
    |⟪querySourceProbe (FrameSpace k) n M R hR P seed hn j
      (boundary (FrameSpace k) n M R hR P seed hn q (frameRows k n M e Q) t),
      ConeValue.sourceMean (fun i j ↦ frameRows k n M e Q j i) j⟫_ℝ| ≤ 1 / 16 ∧
    |⟪queryClockProbe (FrameSpace k) n M R hR P seed hn j
      (boundary (FrameSpace k) n M R hR P seed hn q (frameRows k n M e Q) t),
      ConeValue.sourceMean (fun i j ↦ frameRows k n M e Q j i) j⟫_ℝ| ≤ 1 / 16 ∧
    |⟪finalSourceProbe (FrameSpace k) n M R hR P seed j
      (boundary (FrameSpace k) n M R hR P seed hn q (frameRows k n M e Q) t),
      ConeValue.sourceMean (fun i j ↦ frameRows k n M e Q j i) j⟫_ℝ| ≤ 1 / 16 := by
  let s := boundary (FrameSpace k) n M R hR P seed hn q (frameRows k n M e Q) t
  have hcard : (s.progress.2.card : ℝ) ≤ (n : ℝ) / 4096 :=
    ConeCounter.learned_fraction_le _ (boundary_learned_lt (FrameSpace k) n M R hR P seed hn q _ t)
  have hunseen (i : Fin n) (hi : i ∈ s.progress.2ᶜ) :=
    hno t ht j i (boundary_unseen_not_observed k n M R hR P seed hn q
      (frameRows k n M e Q) e j t i hj (Finset.mem_compl.mp hi))
  have hrow := frameRows_orthonormal k n M e Q j
  have hs := rowMean_small_correlation hn _ hrow s.progress.2
    (querySourceProbe (FrameSpace k) n M R hR P seed hn j s)
    (querySourceProbe_norm_le (FrameSpace k) n M R hR P seed hn j s) hcard
    (fun i hi ↦ (hunseen i hi).1)
  have hc := rowMean_small_correlation hn _ hrow s.progress.2
    (queryClockProbe (FrameSpace k) n M R hR P seed hn j s)
    ((queryClockProbe_norm_le (FrameSpace k) n M R hR P seed hn j s).trans (by norm_num)) hcard
    (fun i hi ↦ (hunseen i hi).2.1)
  have hf := rowMean_small_correlation hn _ hrow s.progress.2
    (finalSourceProbe (FrameSpace k) n M R hR P seed j s)
    ((finalSourceProbe_norm_le (FrameSpace k) n M R hR P seed j s).trans (by norm_num)) hcard
    (fun i hi ↦ (hunseen i hi).2.2)
  exact ⟨hs, hc, hf⟩

theorem noLeak_goodBefore (seed : Ω) (hn : 0 < n) (q : ℝ) (e : Fin n ↪ Fin k)
    (Q : Fin (M + 1) → OrthogonalGroup k) (T : ℕ)
    (hno : NoLeak k n M R hR P seed hn q e Q T) :
    GoodBefore (FrameSpace k) n M R hR P seed hn q (fun i j ↦ frameRows k n M e Q j i) T := by
  intro t ht o ha j hj
  have hh := noLeak_source_correlations k n M R hR P seed hn q e Q T hno t ht.le j hj
  have hquery : nextQuery (FrameSpace k) n M R hR P seed hn
      (boundary (FrameSpace k) n M R hR P seed hn q (frameRows k n M e Q) t) = o := by
    simp only [nextQuery, ha, actionQuery, Sum.elim_inr, id_eq]
  change |⟪sourceProbe (FrameSpace k) M j (nextQuery (FrameSpace k) n M R hR P seed hn
      (boundary (FrameSpace k) n M R hR P seed hn q (frameRows k n M e Q) t)).2.1,
      ConeValue.sourceMean (fun i j ↦ frameRows k n M e Q j i) j⟫_ℝ| ≤ 1 / 16 ∧
    |⟪clockProbe (FrameSpace k) M j (nextQuery (FrameSpace k) n M R hR P seed hn
      (boundary (FrameSpace k) n M R hR P seed hn q (frameRows k n M e Q) t)).2.1,
      ConeValue.sourceMean (fun i j ↦ frameRows k n M e Q j i) j⟫_ℝ| ≤ 1 / 16 ∧ _ at hh
  rw [hquery] at hh
  constructor
  · have hb := (le_abs_self _).trans hh.1
    exact hb.trans_lt (by norm_num)
  · exact hh.2.1.trans_lt (by norm_num)

theorem noLeak_policy_output_eq (seed : Ω) (hn : 0 < n) (L : ℝ) (hL : 0 < L)
    (q : ℝ) (hq : 1 ≤ q) (e : Fin n ↪ Fin k)
    (Q : Fin (M + 1) → OrthogonalGroup k) (T : ℕ)
    (hbudget : (T : ℝ) < (n : ℝ) * (M + 1 : ℕ) / 4096)
    (hno : NoLeak k n M R hR P seed hn q e Q T) :
    (OraclePolicy.run (Domain (FrameSpace k) M R hR) P
      (oracleResponse (ConeProblem.problem hn L hL R hR q hq
        (fun i j ↦ frameRows k n M e Q j i) (frameRows_orthonormal k n M e Q))) seed T).1 =
      output (FrameSpace k) n M R hR P seed
        (boundary (FrameSpace k) n M R hR P seed hn q (frameRows k n M e Q) T) := by
  exact policy_output_eq_reference (FrameSpace k) n M R hR P seed hn L hL q hq
    (fun i j ↦ frameRows k n M e Q j i) (frameRows_orthonormal k n M e Q) T hbudget
    (noLeak_goodBefore k n M R hR P seed hn q e Q T hno)

theorem noLeak_not_stationary (seed : Ω) (hn : 0 < n) (q : ℝ)
    (hR1 : 1 ≤ R) (hq : 16 ≤ q) (hrel : Real.sqrt (n : ℝ) = q * R)
    (hq2 : Real.sqrt (n : ℝ) ≤ q ^ 2) (e : Fin n ↪ Fin k)
    (Q : Fin (M + 1) → OrthogonalGroup k) (T : ℕ)
    (hbudget : (T : ℝ) < (n : ℝ) * (M + 1 : ℕ) / 4096)
    (hno : NoLeak k n M R hR P seed hn q e Q T) :
    ¬ StationaryOutput
      (ConeProblem.problem hn ConeSmooth.individualConstant ConeSmooth.individualConstant_pos R hR q (by linarith)
        (fun i j ↦ frameRows k n M e Q j i) (frameRows_orthonormal k n M e Q))
      (OraclePolicy.run (Domain (FrameSpace k) M R hR) P
        (oracleResponse (ConeProblem.problem hn ConeSmooth.individualConstant ConeSmooth.individualConstant_pos R hR q (by linarith)
          (fun i j ↦ frameRows k n M e Q j i) (frameRows_orthonormal k n M e Q))) seed T).1 := by
  intro hstat
  have hout := noLeak_policy_output_eq k n M R hR P seed hn ConeSmooth.individualConstant
    ConeSmooth.individualConstant_pos q (by linarith) e Q T hbudget hno
  rw [hout] at hstat
  have hf := boundary_unfinished (FrameSpace k) n M R hR P seed hn q (frameRows k n M e Q) T hbudget
  let j : Fin (M + 1) := ⟨_, hf⟩
  have hsmall := (noLeak_source_correlations k n M R hR P seed hn q e Q T hno T le_rfl j le_rfl).2.2
  have hlarge := (ConeSmooth.stationary_output_source_probe hn hR1 hq hrel hq2
    (fun i j ↦ frameRows k n M e Q j i) (frameRows_orthonormal k n M e Q) _ hstat j).2
  have hh := le_abs_self ⟪finalSourceProbe (FrameSpace k) n M R hR P seed j
    (boundary (FrameSpace k) n M R hR P seed hn q (frameRows k n M e Q) T),
    ConeValue.sourceMean (fun i j ↦ frameRows k n M e Q j i) j⟫_ℝ
  change 1 / 4 ≤ ⟪finalSourceProbe (FrameSpace k) n M R hR P seed j
    (boundary (FrameSpace k) n M R hR P seed hn q (frameRows k n M e Q) T),
    ConeValue.sourceMean (fun i j ↦ frameRows k n M e Q j i) j⟫_ℝ at hlarge
  linarith

end

end NCConcave16991.Haar.ConeMachine
