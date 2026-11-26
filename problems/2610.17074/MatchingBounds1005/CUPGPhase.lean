import MatchingBounds1005.CUPGPhaseDecrease
import MatchingBounds1005.CUPGFiniteChoice

/-! A complete finite accelerated phase, including all explicitly evaluated
escape candidates. Its decrease is proved from the actual objective. -/
noncomputable section
open scoped InnerProductSpace ContDiff

namespace MatchingBounds1005.CUPG
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def phasePoints (f : E → ℝ) (q α τ : ℝ) (start : E) (N n : ℕ) : List E :=
  let g := regularized f α start
  let y := fun j => (estimateRun g q α start j).point
  let x := fun j => query q (estimateRun g q α start j)
  let w := witnessPoint g q α start n
  [w] ++ (List.range (N + 1)).map y ++
    (List.range N).map (fun j => guardNear (y (j + 1)) (y j)) ++
    (List.range N).map (fun j => guardFar (y (j + 1)) (y j)) ++
    (List.range N).map (fun j => escapeMinus (y j) (x j) (16 * τ)) ++
    (List.range N).map (fun j => escapePlus (y j) (x j) (16 * τ)) ++
    (List.range N).map (fun j => escapeMinus w (x j) (16 * τ)) ++
    (List.range N).map (fun j => escapePlus w (x j) (16 * τ))

def phaseBest (f : E → ℝ) (q α τ : ℝ) (start : E) (N n : ℕ) : E :=
  bestPoint f start (phasePoints f q α τ start N n)

theorem phaseBest_le_start (f : E → ℝ) (q α τ : ℝ) (start : E) (N n : ℕ) :
    f (phaseBest f q α τ start N n) ≤ f start := bestPoint_le_start _ _ _

theorem phaseBest_le_point (f : E → ℝ) (q α τ : ℝ) (start : E) (N n : ℕ)
    (u : E) (hu : u ∈ phasePoints f q α τ start N n) :
    f (phaseBest f q α τ start N n) ≤ f u := bestPoint_le_mem _ _ _ _ hu

theorem phaseBest_nonconvex_decrease {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    {L₁ L₃ α q τ : ℝ} (hα : 0 < α) (hq : 0 < q) (hqone : q ≤ 1)
    (hτ : 0 < τ) (hL₃ : 0 ≤ L₃) (hscale : (L₁ + 2 * α) * q ^ 2 = α)
    (hstep : L₃ * (16 * τ) ^ 2 ≤ α)
    (hsm : SmoothUpper f L₁) (hdir : DirectionalLip f 3 L₃)
    (start : E) (N n : ℕ) (hn : n ≤ N)
    (hpast : ∀ j < n, ProgressPass (regularized f α start) q α (L₁ + 2 * α) start j)
    (hfail : ¬ ProgressPass (regularized f α start) q α (L₁ + 2 * α) start n) :
    f (phaseBest f q α τ start N n) ≤ f start - α * τ ^ 2 := by
  let b := phaseBest f q α τ start N n
  have hmem (u : E) (hu : u ∈ phasePoints f q α τ start N n) : f b ≤ f u :=
    phaseBest_le_point f q α τ start N n u hu
  have hYmem (j : ℕ) (hj : j < N + 1) :
      (estimateRun (regularized f α start) q α start j).point ∈ phasePoints f q α τ start N n := by
    have hm := List.mem_map_of_mem (f := fun i => (estimateRun (regularized f α start) q α start i).point)
      (List.mem_range.mpr hj)
    simp only [phasePoints, List.mem_append]
    tauto
  have hNmem (j : ℕ) (hj : j < N) : guardNear
      (estimateRun (regularized f α start) q α start (j + 1)).point
      (estimateRun (regularized f α start) q α start j).point ∈ phasePoints f q α τ start N n := by
    have hm := List.mem_map_of_mem (f := fun i => guardNear
      (estimateRun (regularized f α start) q α start (i + 1)).point
      (estimateRun (regularized f α start) q α start i).point) (List.mem_range.mpr hj)
    simp only [phasePoints, List.mem_append]
    tauto
  have hFmem (j : ℕ) (hj : j < N) : guardFar
      (estimateRun (regularized f α start) q α start (j + 1)).point
      (estimateRun (regularized f α start) q α start j).point ∈ phasePoints f q α τ start N n := by
    have hm := List.mem_map_of_mem (f := fun i => guardFar
      (estimateRun (regularized f α start) q α start (i + 1)).point
      (estimateRun (regularized f α start) q α start i).point) (List.mem_range.mpr hj)
    simp only [phasePoints, List.mem_append]
    tauto
  obtain ⟨j, hj, u, hu, hd⟩ := nonconvex_phase_decrease hf hα hq hqone hτ hL₃
    hscale hstep hsm hdir start b n hpast hfail (phaseBest_le_start _ _ _ _ _ _ _)
    (fun j hj => hmem _ (hYmem j (by omega)))
    (hmem _ (by simp [phasePoints]))
    (fun j hj => hmem _ (hNmem j (by omega)))
    (fun j hj => hmem _ (hFmem j (by omega)))
  have hminus : f b ≤ f (escapeMinus u
      (query q (estimateRun (regularized f α start) q α start j)) (16 * τ)) := by
    apply hmem
    have hjN : j < N := by omega
    rcases hu with rfl | rfl
    · have hm := List.mem_map_of_mem (f := fun i => escapeMinus
        (estimateRun (regularized f α start) q α start i).point
        (query q (estimateRun (regularized f α start) q α start i)) (16 * τ)) (List.mem_range.mpr hjN)
      simp only [phasePoints, List.mem_append]
      tauto
    · have hm := List.mem_map_of_mem (f := fun i => escapeMinus
        (witnessPoint (regularized f α start) q α start n)
        (query q (estimateRun (regularized f α start) q α start i)) (16 * τ)) (List.mem_range.mpr hjN)
      simp only [phasePoints, List.mem_append]
      tauto
  have hplus : f b ≤ f (escapePlus u
      (query q (estimateRun (regularized f α start) q α start j)) (16 * τ)) := by
    apply hmem
    have hjN : j < N := by omega
    rcases hu with rfl | rfl
    · have hm := List.mem_map_of_mem (f := fun i => escapePlus
        (estimateRun (regularized f α start) q α start i).point
        (query q (estimateRun (regularized f α start) q α start i)) (16 * τ)) (List.mem_range.mpr hjN)
      simp only [phasePoints, List.mem_append]
      tauto
    · have hm := List.mem_map_of_mem (f := fun i => escapePlus
        (witnessPoint (regularized f α start) q α start n)
        (query q (estimateRun (regularized f α start) q α start i)) (16 * τ)) (List.mem_range.mpr hjN)
      simp only [phasePoints, List.mem_append]
      tauto
  exact (min_eq_left (le_min hminus hplus) ▸ hd)

def stoppedIndex (f : E → ℝ) (q α L ε : ℝ) (start : E) (N : ℕ) : ℕ :=
  @firstIndex (Stopped (regularized f α start) q α L (ε / 10) start) (Classical.decPred _) N

def phasePoint (f : E → ℝ) (q α τ L ε : ℝ) (start : E) (N : ℕ) : E := by
  classical
  let n := stoppedIndex f q α L ε start N
  exact if ProgressPass (regularized f α start) q α L start n then
    (estimateRun (regularized f α start) q α start n).point
  else phaseBest f q α τ start N n

theorem phasePoint_progress {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    {L₁ L₃ α q τ ε Δ D : ℝ} (hα : 0 < α) (hq : 0 < q) (hqone : q ≤ 1)
    (hτ : 0 < τ) (hε : 0 < ε) (hL₃ : 0 ≤ L₃)
    (hscale : (L₁ + 2 * α) * q ^ 2 = α) (hstep : L₃ * (16 * τ) ^ 2 ≤ α)
    (hsm : SmoothUpper f L₁) (hdir : DirectionalLip f 3 L₃)
    (hD : D ≤ α * τ ^ 2) (hD' : D ≤ ε ^ 2 / (5 * α)) (hDnonneg : 0 ≤ D)
    (start : E) (N : ℕ) (hgap : ∀ z, f start - f z ≤ Δ)
    (hcap : 2 * (L₁ + 2 * α) * Δ * Real.exp (-q * N) ≤ (ε / 10) ^ 2) :
    let out := phasePoint f q α τ (L₁ + 2 * α) ε start N
    f out ≤ f start ∧ (ε < ‖gradient f out‖ → f out ≤ f start - D) := by
  classical
  let g := regularized f α start
  let n := stoppedIndex f q α (L₁ + 2 * α) ε start N
  have hn : n ≤ N := firstIndex_le _ _
  have hL : 0 ≤ L₁ + 2 * α := by nlinarith [sq_nonneg q]
  have hsN : Stopped g q α (L₁ + 2 * α) (ε / 10) start N :=
    stopped_at_cap g (by positivity) hL start N (regularized_gap_le hα.le start hgap _) hcap
  have hs : Stopped g q α (L₁ + 2 * α) (ε / 10) start n := firstIndex_spec _ N hsN
  have hpast : ∀ j < n, ProgressPass g q α (L₁ + 2 * α) start j := by
    intro j hj
    have hh := firstIndex_min (Stopped g q α (L₁ + 2 * α) (ε / 10) start) N j hj
    exact not_not.mp (not_or.mp hh).1
  let out := if ProgressPass g q α (L₁ + 2 * α) start n then
      (estimateRun g q α start n).point else phaseBest f q α τ start N n
  change f out ≤ f start ∧ (ε < ‖gradient f out‖ → f out ≤ f start - D)
  dsimp only [out]
  by_cases hp : ProgressPass g q α (L₁ + 2 * α) start n
  · simp only [if_pos hp]
    have hv : regularized f α start (estimateRun g q α start n).point ≤ f start := by
      simpa [g, regularized] using hp.1
    have hvf : f (estimateRun g q α start n).point ≤ f start := by
      have hh : 0 ≤ α * ‖(estimateRun g q α start n).point - start‖ ^ 2 := by positivity
      unfold regularized at hv
      linarith
    refine ⟨hvf, fun hlarge => ?_⟩
    have hg : ‖gradient g (estimateRun g q α start n).point‖ ≤ ε / 10 := hs.resolve_left (not_not.mpr hp)
    have hd := regularized_small_gradient_decrease (hf.differentiable (by norm_num))
      hα hε start _ hv hg hlarge
    linarith
  · simp only [if_neg hp]
    have hd := phaseBest_nonconvex_decrease hf hα hq hqone hτ hL₃ hscale hstep hsm hdir
      start N n hn hpast hp
    constructor
    · linarith
    · intro _; linarith

end MatchingBounds1005.CUPG
