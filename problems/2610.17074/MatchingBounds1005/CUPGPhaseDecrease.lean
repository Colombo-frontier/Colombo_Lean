import MatchingBounds1005.CUPGPhaseGeometry
import MatchingBounds1005.CUPGPhysicalEscape
import MatchingBounds1005.CUPGWitness

/-! # The verified nonconvex branch of an actual accelerated phase

`best` is a minimum of a specified finite list of already evaluated points.
Only those explicit minimum comparisons are inputs; the decrease conclusion
is derived from the true AGD recurrence and true first-order witness.
-/
noncomputable section
open scoped InnerProductSpace ContDiff

namespace MatchingBounds1005.CUPG
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem nonconvex_phase_decrease {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    {L₁ L₃ α q τ : ℝ} (hα : 0 < α) (hq : 0 < q) (hqone : q ≤ 1)
    (hτ : 0 < τ) (hL₃ : 0 ≤ L₃) (hscale : (L₁ + 2 * α) * q ^ 2 = α)
    (hstep : L₃ * (16 * τ) ^ 2 ≤ α)
    (hsm : SmoothUpper f L₁) (hdir : DirectionalLip f 3 L₃)
    (start best : E) (n : ℕ)
    (hpast : ∀ j < n, ProgressPass (regularized f α start) q α (L₁ + 2 * α) start j)
    (hfail : ¬ ProgressPass (regularized f α start) q α (L₁ + 2 * α) start n)
    (hbestStart : f best ≤ f start)
    (hbestY : ∀ j < n, f best ≤ f (estimateRun (regularized f α start) q α start j).point)
    (hbestW : f best ≤ f (witnessPoint (regularized f α start) q α start n))
    (hbestNear : ∀ j, j + 1 < n → f best ≤ f (guardNear
      (estimateRun (regularized f α start) q α start (j + 1)).point
      (estimateRun (regularized f α start) q α start j).point))
    (hbestFar : ∀ j, j + 1 < n → f best ≤ f (guardFar
      (estimateRun (regularized f α start) q α start (j + 1)).point
      (estimateRun (regularized f α start) q α start j).point)) :
    ∃ j < n, ∃ u : E,
      (u = (estimateRun (regularized f α start) q α start j).point ∨
        u = witnessPoint (regularized f α start) q α start n) ∧
      let v := query q (estimateRun (regularized f α start) q α start j)
      min (f best) (min (f (escapeMinus u v (16 * τ))) (f (escapePlus u v (16 * τ)))) ≤
        f start - α * τ ^ 2 := by
  let g := regularized f α start
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hgsm := regularized_smoothUpper hd hsm α start
  obtain ⟨j, hj, u, hu, hgu, hnc⟩ := bounded_progress_witness g hq hqone hα hscale hgsm start n hpast hfail
  refine ⟨j, hj, u, hu, ?_⟩
  let v := query q (estimateRun g q α start j)
  change min (f best) (min (f (escapeMinus u v (16 * τ))) (f (escapePlus u v (16 * τ)))) ≤ _
  by_cases hlow : f best ≤ f start - α * τ ^ 2
  · exact (min_le_left _ _).trans hlow
  have hfloor : f start - α * τ ^ 2 ≤ f best := le_of_not_ge hlow
  have hgstart : g start = f start := by simp [g, regularized]
  have hgu' : g u ≤ f start := by simpa only [hgstart] using hgu
  have hyVal (i : ℕ) (hi : i < n) : g (estimateRun g q α start i).point ≤ f start := by
    have hh : g (estimateRun g q α start i).point ≤ g start := (hpast i hi).1
    rwa [hgstart] at hh
  have hyRad (i : ℕ) (hi : i < n) : ‖(estimateRun g q α start i).point - start‖ ≤ τ :=
    proximal_radius hα hτ.le start _ (hyVal i hi) (hfloor.trans (hbestY i hi))
  have hfu : f u ≤ f start := by
    have hn : 0 ≤ α * ‖u - start‖ ^ 2 := by positivity
    change f u + α * ‖u - start‖ ^ 2 ≤ f start at hgu'
    linarith
  have huRad : ‖u - start‖ ≤ τ := by
    apply proximal_radius hα hτ.le start u hgu'
    rcases hu with rfl | rfl
    · exact hfloor.trans (hbestY j hj)
    · exact hfloor.trans hbestW
  have hguardScale : 16 * L₃ * τ ^ 2 ≤ α := by
    have hp : 0 ≤ L₃ * τ ^ 2 := by positivity
    nlinarith only [hstep, hp]
  have hvboth : ‖v - start‖ ≤ 3 * τ ∧ f v ≤ f start + 14 * α * τ ^ 2 := by
    cases j with
    | zero =>
      have he : v = start := query_run_zero g hq.le start
      rw [he]
      constructor
      · simp; positivity
      · have hp : 0 ≤ 14 * α * τ ^ 2 := by positivity
        linarith
    | succ j =>
      have hv : v = (estimateRun g q α start (j + 1)).point +
          ((1 - q) / (1 + q)) • ((estimateRun g q α start (j + 1)).point -
            (estimateRun g q α start j).point) :=
        query_step_extrapolate g hq.le hα.ne' _
      rw [hv]
      have hj' : j < n := by omega
      have hcur := hyRad (j + 1) hj
      have hprev := hyRad j hj'
      have hω := momentum_bounds hq.le hqone
      refine ⟨extrapolation_radius hτ.le hω.1 hω.2 start _ _ hcur hprev, ?_⟩
      apply extrapolation_value hf hL₃ hα hτ.le hω.1 hω.2 hguardScale hdir start _ _
      · have hh := hyVal (j + 1) hj
        change f _ + α * ‖_ - start‖ ^ 2 ≤ f start at hh
        have hn : 0 ≤ α * ‖(estimateRun g q α start (j + 1)).point - start‖ ^ 2 := by positivity
        linarith
      · have hh := hyVal j hj'
        change f _ + α * ‖_ - start‖ ^ 2 ≤ f start at hh
        have hn : 0 ≤ α * ‖(estimateRun g q α start j).point - start‖ ^ 2 := by positivity
        linarith
      · exact hfloor.trans (hbestNear j hj)
      · exact hfloor.trans (hbestFar j hj)
      · exact hcur
      · exact hprev
  have hdist : ‖u - v‖ ≤ (16 * τ) / 2 := by
    have he : u - v = (u - start) - (v - start) := by abel
    rw [he]
    exact (norm_sub_le _ _).trans (by linarith [hvboth.1])
  have hnc' := regularized_violation hd α start u v hnc
  have hesc := physical_symmetric_escape hf hα hL₃ (by positivity : 0 < 16 * τ)
    hdir u v hnc' hdist hstep
  have hmax : max (f v) (f u) ≤ f start + 14 * α * τ ^ 2 := by
    apply max_le hvboth.2
    have hn : 0 ≤ 14 * α * τ ^ 2 := by positivity
    linarith
  apply (min_le_right _ _).trans
  have hp : 0 ≤ α * τ ^ 2 := by positivity
  nlinarith only [hesc, hmax, hp]

end MatchingBounds1005.CUPG
