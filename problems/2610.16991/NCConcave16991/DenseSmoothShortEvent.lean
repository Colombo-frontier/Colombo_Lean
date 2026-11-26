import NCConcave16991.DenseSmoothShortStage
import NCConcave16991.DenseSmoothCensoredTrace
import NCConcave16991.DenseSmoothRevelationCurrent
import NCConcave16991.DenseSmoothProbeAlignment

/-! # Every actual short completed stage gives a censored static-bank event -/

namespace NCConcave16991.DenseSmooth.Revelation

noncomputable section

open DenseWeakHiding
open scoped InnerProductSpace

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable (n T D : ℕ) (hn : 0 < n) (ρ : ℝ) (hρ : 0 < ρ)
  {Ω : Type*} [MeasurableSpace Ω]
  (P : OraclePolicy.AdaptivePolicy (Domain n T hn ρ hρ) (n := n)
    (dx := primalDimension (CensoredSpace D) T) Ω)

theorem short_completion_censored_witness (seed : Ω) (A : Table (CensoredSpace D) n T ρ)
    (j : Fin T) (N e r : ℕ)
    (he : frontier (CensoredSpace D) n T hn ρ hρ (runWithTable (CensoredSpace D) n T hn ρ hρ P seed A e) = j.val)
    (hN : j.val < frontier (CensoredSpace D) n T hn ρ hρ (runWithTable (CensoredSpace D) n T hn ρ hρ P seed A N))
    (hshort : (runWithTable (CensoredSpace D) n T hn ρ hρ P seed A N).assigned j.castSucc < r) :
    ∃ u < N, e ≤ u ∧
      completion (CensoredSpace D) n T hn ρ hρ P seed A
        (runWithTable (CensoredSpace D) n T hn ρ hρ P seed A u) = true ∧
      (runWithTable (CensoredSpace D) n T hn ρ hρ P seed A u).assigned j.castSucc + 1 < r ∧
      runWithTable (CensoredSpace D) n T hn ρ hρ P seed A u =
        censoredRunFrom (CensoredSpace D) n T hn ρ hρ P seed (fun i ↦ A.row i j.castSucc)
          (runWithTable (CensoredSpace D) n T hn ρ hρ P seed A e) (u - e) ∧
      stageIndex (CensoredSpace D) n T hn ρ hρ
        (runWithTable (CensoredSpace D) n T hn ρ hρ P seed A u) = j.castSucc := by
  obtain ⟨u,hu,hfu,hc,hcost⟩ := completed_stage_witness (CensoredSpace D) n T hn ρ hρ P seed A j N hN
  have hpost := completion_true_frontier (CensoredSpace D) n T hn ρ hρ P seed A _ hc
  change frontier (CensoredSpace D) n T hn ρ hρ
    (runWithTable (CensoredSpace D) n T hn ρ hρ P seed A (u + 1)) = _ at hpost
  have heu : e ≤ u := by
    by_contra h
    have hh := run_frontier_mono (CensoredSpace D) n T hn ρ hρ P seed A (show u + 1 ≤ e by omega)
    change frontier (CensoredSpace D) n T hn ρ hρ (runWithTable (CensoredSpace D) n T hn ρ hρ P seed A (u + 1)) ≤
      frontier (CensoredSpace D) n T hn ρ hρ (runWithTable (CensoredSpace D) n T hn ρ hρ P seed A e) at hh
    omega
  have hv : frontier (CensoredSpace D) n T hn ρ hρ
      (runWithTable (CensoredSpace D) n T hn ρ hρ P seed A u) < T + 1 := by rw [hfu]; omega
  have hidx : stageIndex (CensoredSpace D) n T hn ρ hρ
      (runWithTable (CensoredSpace D) n T hn ρ hρ P seed A u) = j.castSucc :=
    Fin.ext ((Nat.mod_eq_of_lt hv).trans hfu)
  exact ⟨u,hu,heu,hc,by omega,
    same_stage_eq_censored (CensoredSpace D) n T hn ρ hρ P seed A j.castSucc e u heu he hfu,hidx⟩

theorem short_completion_initialized_event (hD : 0 < D) (seed : Ω)
    (A : Table (CensoredSpace D) n T ρ) (j : Fin T) (N e r : ℕ) (i₀ : Fin n)
    (start : CensoredSpace D → State (CensoredSpace D) n T hn ρ hρ)
    (hstart : ∀ a, frontier (CensoredSpace D) n T hn ρ hρ (start a) = j.val)
    (table : Fin n → FreshCompiler.Reply D) (hrow : ∀ i, normalizedReply (table i) = A.row i j.castSucc)
    (hentry : runWithTable (CensoredSpace D) n T hn ρ hρ P seed A e = start (normalizedReply (table i₀)))
    (labels : Fin D → Fin 2)
    (hdir : A.direction j.castSucc = normalizedSignVector (fun d ↦ hiddenSign (labels d)))
    (hN : j.val < frontier (CensoredSpace D) n T hn ρ hρ (runWithTable (CensoredSpace D) n T hn ρ hρ P seed A N))
    (hshort : (runWithTable (CensoredSpace D) n T hn ρ hρ P seed A N).assigned j.castSucc < r) :
    ∃ s ∈ FreshCompiler.cutTrace (initializedBitsRequest n T D hn ρ hρ P seed i₀)
      (initializedBitsAdvance n T D hn ρ hρ P seed start) table r (N + 1) (.inl ()),
      (5 / 32 : ℝ) * Real.sqrt (D : ℝ) ≤ signedSum
        (initializedProbe n T D hn ρ hρ
          (fun s d ↦ queryProbe (CensoredSpace D) n T hn ρ hρ P seed j.castSucc s d) s) labels := by
  have he : frontier (CensoredSpace D) n T hn ρ hρ (runWithTable (CensoredSpace D) n T hn ρ hρ P seed A e) = j.val := by
    rw [hentry]
    exact hstart _
  obtain ⟨u,hu,heu,hc,hcost,hcens,hidx⟩ :=
    short_completion_censored_witness n T D hn ρ hρ P seed A j N e r he hN hshort
  have hcorrect := run_currentCorrect (CensoredSpace D) n T hn ρ hρ P seed A e
  rw [hentry] at hcorrect
  have hccost : (censoredRunFrom (CensoredSpace D) n T hn ρ hρ P seed (fun i ↦ A.row i j.castSucc)
      (start (normalizedReply (table i₀))) (u - e)).assigned j.castSucc + 1 < r := by
    rwa [← hentry,← hcens]
  have hmem := initialized_censored_mem_cutTrace n T D hn ρ hρ P seed i₀ start A j.castSucc table hrow
    hcorrect hstart (N + 1) r (u - e) (by omega) hccost
  refine ⟨.inr (runWithTable (CensoredSpace D) n T hn ρ hρ P seed A u),?_,?_⟩
  · simpa only [← hentry,← hcens] using hmem
  · change (5 / 32 : ℝ) * Real.sqrt (D : ℝ) ≤ signedSum
      (fun d ↦ queryProbe (CensoredSpace D) n T hn ρ hρ P seed j.castSucc
        (runWithTable (CensoredSpace D) n T hn ρ hρ P seed A u) d) labels
    have hh := completion_query_alignment (CensoredSpace D) n T hn ρ hρ P seed A _ hc
    rw [hidx,hdir,normalizedSignVector_inner] at hh
    have hp : 0 < Real.sqrt (D : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hD)
    have hm := mul_lt_mul_of_pos_right hh hp
    apply le_of_lt
    convert hm using 1 <;> field_simp

theorem short_completion_empty_event (hD : 0 < D) (seed : Ω)
    (A : Table (CensoredSpace D) n T ρ) (j : Fin T) (N e r : ℕ)
    (s₀ : State (CensoredSpace D) n T hn ρ hρ)
    (hs₀ : frontier (CensoredSpace D) n T hn ρ hρ s₀ = j.val)
    (table : Fin n → FreshCompiler.Reply D) (hrow : ∀ i, normalizedReply (table i) = A.row i j.castSucc)
    (hentry : runWithTable (CensoredSpace D) n T hn ρ hρ P seed A e = s₀)
    (labels : Fin D → Fin 2)
    (hdir : A.direction j.castSucc = normalizedSignVector (fun d ↦ hiddenSign (labels d)))
    (hN : j.val < frontier (CensoredSpace D) n T hn ρ hρ (runWithTable (CensoredSpace D) n T hn ρ hρ P seed A N))
    (hshort : (runWithTable (CensoredSpace D) n T hn ρ hρ P seed A N).assigned j.castSucc < r) :
    ∃ s ∈ FreshCompiler.cutTrace (bitsRequest n T D hn ρ hρ P seed)
      (bitsAdvance n T D hn ρ hρ P seed) table r (N + 1) s₀,
      (5 / 32 : ℝ) * Real.sqrt (D : ℝ) ≤ signedSum
        (fun d ↦ queryProbe (CensoredSpace D) n T hn ρ hρ P seed j.castSucc s d) labels := by
  have he : frontier (CensoredSpace D) n T hn ρ hρ (runWithTable (CensoredSpace D) n T hn ρ hρ P seed A e) = j.val := by
    rwa [hentry]
  obtain ⟨u,hu,heu,hc,hcost,hcens,hidx⟩ :=
    short_completion_censored_witness n T D hn ρ hρ P seed A j N e r he hN hshort
  have hcorrect := run_currentCorrect (CensoredSpace D) n T hn ρ hρ P seed A e
  rw [hentry] at hcorrect
  have hccost : (censoredRunFrom (CensoredSpace D) n T hn ρ hρ P seed (fun i ↦ A.row i j.castSucc)
      s₀ (u - e)).assigned j.castSucc < r := by
    rw [← hentry,← hcens]
    omega
  have hmem := censored_mem_cutTrace n T D hn ρ hρ P seed A s₀ hcorrect j.castSucc hs₀ table hrow
    (N + 1) r (u - e) (by omega) hccost
  refine ⟨runWithTable (CensoredSpace D) n T hn ρ hρ P seed A u,?_,?_⟩
  · simpa only [← hentry,← hcens] using hmem
  · have hh := completion_query_alignment (CensoredSpace D) n T hn ρ hρ P seed A _ hc
    rw [hidx,hdir,normalizedSignVector_inner] at hh
    have hp : 0 < Real.sqrt (D : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hD)
    have hm := mul_lt_mul_of_pos_right hh hp
    apply le_of_lt
    convert hm using 1 <;> field_simp

end
end NCConcave16991.DenseSmooth.Revelation
