import NCConcave16991.GlobalHardStateRestriction
import NCConcave16991.GlobalHardSectionGradient
import NCConcave16991.GlobalHardLowState

/-! # State estimates from the actual full primal gradient -/

namespace NCConcave16991.GlobalHard

noncomputable section
open LocalizationScalar LocalizationRadial
open scoped BigOperators InnerProductSpace ContDiff

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048
set_option maxSynthPendingDepth 4
set_option maxHeartbeats 800000

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {M N : ℕ} (V : Fin M → Fin (N + 1) → Type*)
  [∀ j k, NormedAddCommGroup (V j k)] [∀ j k, InnerProductSpace ℝ (V j k)]
  [∀ j k, CompleteSpace (V j k)]

theorem stateSection_split (z : Joint V) (j : Fin M) (s : V j (Fin.last N)) :
    stateSection V z j s = WithLp.toLp 2
      (WithLp.fst z + primalStateInjection V j (s - stateProj V j z), WithLp.snd z) := by
  apply WithLp.ofLp_injective 2
  change (WithLp.fst z + primalStateInjection V j (s - stateProj V j z), WithLp.snd z + 0) = _
  simp

theorem entryPair_abs_bound (u : ∀ j, V j 0) (hu : ∀ j, ‖u j‖ = 1) (z : Joint V) (j : Fin M) :
    |entryPair V u z j| ≤ 42 := by
  have hb := (radialCap_value_bounds (by norm_num : (0 : ℝ) < 21) (aProj V j z)).trans (min_le_right _ _)
  have hh := abs_real_inner_le_norm (u j) (radialCap 21 (aProj V j z))
  rw [hu j, one_mul] at hh
  exact hh.trans (by norm_num at hb ⊢; exact hb)

variable (B : ∀ j : Fin M, ∀ t : Fin N,
    BranchGeometry.BranchFamily (ι := ι) (V j t.castSucc) (V j t.succ))
  (u : ∀ j, V j 0) (v : ∀ j, V j (Fin.last N))

def primalAverageSection (d r μ : ℝ) (w : Dual V) (x : Primal V) : ℝ :=
  average V B u v d r μ (WithLp.toLp 2 (x, w))

theorem primalAverageSection_contDiff (d r μ : ℝ) (w : Dual V) :
    ContDiff ℝ ∞ (primalAverageSection V B u v d r μ w) := by
  have hc : ContDiff ℝ ∞ (fun x : Primal V ↦ WithLp.toLp 2 (x, w)) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ (Primal V) (Dual V)).symm.contDiff.comp
      (contDiff_id.prodMk contDiff_const)
  exact (average_contDiff V B u v d r μ).comp hc

/-- The actual state gradient is a contraction of the actual primal gradient. -/
theorem stateObjectiveAt_gradient_le (d r μ : ℝ) (z : Joint V) (j : Fin M) :
    ‖gradient (stateObjectiveAt V u v z j) (stateProj V j z)‖ ≤
      ‖gradient (primalAverageSection V B u v d r μ (WithLp.snd z)) (WithLp.fst z)‖ := by
  apply isometric_section_gradient_le _ _ (primalStateInjection V j) _ _
    (average V B u v d r μ z - stateObjectiveAt V u v z j (stateProj V j z))
  · exact (primalAverageSection_contDiff V B u v d r μ (WithLp.snd z)).differentiable (by simp) _
  · intro s
    change average V B u v d r μ (WithLp.toLp 2
      (WithLp.fst z + primalStateInjection V j (s - stateProj V j z), WithLp.snd z)) = _
    rw [← stateSection_split]
    exact average_stateSection_eq V B u v d r μ z j s

/-- Every literal state is in the paper's low or high regime. -/
theorem average_state_classification (d r μ : ℝ) (z : Joint V)
    (hu : ∀ j, ‖u j‖ = 1) (hv : ∀ j, ‖v j‖ = 1)
    (hg : ‖gradient (primalAverageSection V B u v d r μ (WithLp.snd z)) (WithLp.fst z)‖ ≤ 1 / 20)
    (j : Fin M) :
    (-1 / 10 < score V v j z ∧ score V v j z ≤ 1 / 5) ∨ 1 ≤ score V v j z := by
  have hs := (stateObjectiveAt_gradient_le V B u v d r μ z j).trans hg
  have he := entryPair_abs_bound V u hu z j
  by_cases hj : j.val + 1 < M
  · let k : Fin M := ⟨j.val + 1, hj⟩
    have he' := entryPair_abs_bound V u hu z k
    have hx' := exitPair_abs_bound (stateProj V k z) (bProj V k z)
    simp only [stateObjectiveAt, dif_pos hj] at hs
    exact localStateObjective_classification (v j) (bProj V j z) (hv j) _ _ _ _ _ (stateProj V j z) he he' hx' hs
  · simp only [stateObjectiveAt, dif_neg hj] at hs
    exact localStateObjective_classification (v j) (bProj V j z) (hv j) _ _ _ _ _ (stateProj V j z) he (by norm_num) (by norm_num) hs

theorem average_low_state_norm (d r μ : ℝ) (z : Joint V)
    (hu : ∀ j, ‖u j‖ = 1) (hv : ∀ j, ‖v j‖ = 1)
    (hg : ‖gradient (primalAverageSection V B u v d r μ (WithLp.snd z)) (WithLp.fst z)‖ ≤ 1 / 20)
    (j : Fin M) (hl : -1 / 10 < score V v j z) (ht : score V v j z ≤ 1 / 5) :
    ‖stateProj V j z‖ < 1 / 4 := by
  have hs := (stateObjectiveAt_gradient_le V B u v d r μ z j).trans hg
  have he := entryPair_abs_bound V u hu z j
  by_cases hj : j.val + 1 < M
  · let k : Fin M := ⟨j.val + 1, hj⟩
    have he' := entryPair_abs_bound V u hu z k
    have hx' := exitPair_abs_bound (stateProj V k z) (bProj V k z)
    simp only [stateObjectiveAt, dif_pos hj] at hs
    exact localStateObjective_low_norm (v j) (bProj V j z) (hv j) _ _ _ _ _ (stateProj V j z) he he' hx' hl ht hs
  · simp only [stateObjectiveAt, dif_neg hj] at hs
    exact localStateObjective_low_norm (v j) (bProj V j z) (hv j) _ _ _ _ _ (stateProj V j z) he (by norm_num) (by norm_num) hl ht hs

theorem average_no_low_high (d r μ : ℝ) (z : Joint V)
    (hu : ∀ j, ‖u j‖ = 1) (hv : ∀ j, ‖v j‖ = 1)
    (hg : ‖gradient (primalAverageSection V B u v d r μ (WithLp.snd z)) (WithLp.fst z)‖ ≤ 1 / 20)
    (j k : Fin M) (hk : k.val = j.val + 1)
    (hl : -1 / 10 < score V v j z) (ht : score V v j z ≤ 1 / 5) (hn : 1 ≤ score V v k z) : False := by
  have hj : j.val + 1 < M := hk ▸ k.isLt
  have hke : (⟨j.val + 1, hj⟩ : Fin M) = k := Fin.ext hk.symm
  let k0 : Fin M := ⟨j.val + 1, hj⟩
  have hn0 : 1 ≤ score V v k0 z := by simpa only [k0, hke] using hn
  have hs := (stateObjectiveAt_gradient_le V B u v d r μ z j).trans hg
  simp only [stateObjectiveAt, dif_pos hj] at hs
  exact localStateObjective_no_low_high (v j) (bProj V j z) (hv j)
    (precedingScore V v j z) (score V v k0 z) (entryPair V u z j)
    (entryPair V u z k0) (exitPair (stateProj V k0 z) (bProj V k0 z)) (stateProj V j z)
    (entryPair_abs_bound V u hu z j) (entryPair_abs_bound V u hu z k0)
    (exitPair_abs_bound (stateProj V k0 z) (bProj V k0 z)) hl ht hn0 hs

end
end NCConcave16991.GlobalHard
