import NCConcave16991.ConeProblem
import NCConcave16991.ConeRecoveryBranch
import NCConcave16991.ProximalSaddleWitness

/-! # Euclidean source recovery and the actual arbitrary-output Moreau transfer

The last theorem is the analytic transfer from the verified generic Moreau
witness to the concrete instance. Its AS hypothesis is isolated here; the
quantitative IS admissibility proof for the instance is a separate module.
-/

noncomputable section

namespace NCConcave16991.ConeProblem

open ConeValue ConeRecovery Set Metric
open scoped InnerProductSpace BigOperators

set_option backward.isDefEq.respectTransparency false

section Isometry

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]

theorem isometry_comp_hasGradientAt (e : H ≃ₗᵢ[ℝ] G) {f : G → ℝ} {g : G} {x : H}
    (hf : HasGradientAt f g (e x)) :
    HasGradientAt (fun p ↦ f (e p)) (e.symm g) x := by
  have hh := hf.hasFDerivAt.comp x e.toContinuousLinearEquiv.hasFDerivAt
  refine hh.congr_fderiv ?_
  ext h
  simp only [ContinuousLinearMap.comp_apply, InnerProductSpace.toDual_apply_apply]
  exact (e.symm.inner_map_eq_flip g h).symm

end Isometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {n M : ℕ}

theorem decoded_average (hn : 0 < n) (R q : ℝ) (w : Fin n → Fin (M + 1) → E)
    (x : PrimalBlocks E M) (y : Blocks E M) :
    componentAverage (component R q w) (jointPoint (primalCoordinates E M x) (dualCoordinates E M y)) =
      (n : ℝ)⁻¹ * ∑ i, ConeValue.component R q w i x.fst x.snd y := by
  simp only [componentAverage, component, jointPoint, jointComponent, jointCoordinates,
    LinearIsometryEquiv.withLpProdCongr_symm_apply]
  simp only [WithLp.fst, WithLp.snd, LinearIsometryEquiv.symm_apply_apply]

theorem actual_problem_source_recovery (hn : 0 < n) (L : ℝ) (hL : 0 < L)
    (R : ℝ) (hR : 0 < R) (q : ℝ) (hq : 16 ≤ q)
    (w : Fin n → Fin (M + 1) → E) (hw : ∀ j, Orthonormal ℝ (fun i ↦ w i j))
    (x : PrimalSpace (primalDimension E M)) (y : DualSpace (dualDimension E M))
    (hy : y ∈ (dualDomain E M R hR).carrier)
    (hmax : componentAverage (problem hn L hL R hR q (by linarith) w hw).component (jointPoint x y) =
      primalObjective (dualDomain E M R hR) (problem hn L hL R hR q (by linarith) w hw).component x)
    (hsmall : ‖Accelerated.primalMeanGradient (problem hn L hL R hR q (by linarith) w hw) x y‖ ≤ 1 / 1000) :
    ∀ j, ((primalCoordinates E M).symm x).fst j = sourceMean w j := by
  let P := problem hn L hL R hR q (by linarith) w hw
  let xp := (primalCoordinates E M).symm x
  let yp := (dualCoordinates E M).symm y
  have hPc : P.component = component R q w := rfl
  have hsection := P.hasGradientAt_primal_section x y hy
  have hgrad := isometry_comp_hasGradientAt (primalCoordinates E M)
    (f := fun u ↦ componentAverage P.component (jointPoint u y))
    (g := Accelerated.primalMeanGradient P x y)
    (x := xp) (by simpa only [Accelerated.primalMeanGradient, xp, LinearIsometryEquiv.apply_symm_apply] using hsection)
  have hfun : (fun p : PrimalBlocks E M ↦ componentAverage P.component
      (jointPoint (primalCoordinates E M p) y)) =
      (fun p ↦ (n : ℝ)⁻¹ * ∑ i, ConeValue.component R q w i p.fst p.snd yp) := by
    funext p
    rw [hPc]
    have hh := decoded_average hn R q w p yp
    simpa only [yp, LinearIsometryEquiv.apply_symm_apply] using hh
  rw [hfun] at hgrad
  have hraw : ‖gradient (fun p : PrimalBlocks E M ↦
      (n : ℝ)⁻¹ * ∑ i, ConeValue.component R q w i p.fst p.snd yp) xp‖ ≤ 1 / 1000 := by
    rw [hgrad.gradient, LinearIsometryEquiv.norm_map]
    exact hsmall
  apply source_recovery_from_actual_average hn hR hq w hw xp yp _ _ hraw
  · have hyn : ‖y‖ ≤ R := by simpa only [dualDomain, mem_closedBall, dist_zero_right] using hy
    simpa only [mem_closedBall, dist_zero_right, yp, LinearIsometryEquiv.norm_map] using hyn
  · intro b hb
    have hby : dualCoordinates E M b ∈ (dualDomain E M R hR).carrier := by
      simpa only [dualDomain, mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map] using hb
    have hh := componentAverage_le_primalObjective P x (dualCoordinates E M b) hby
    rw [← hmax] at hh
    have hleft := decoded_average hn R q w xp b
    have hright := decoded_average hn R q w xp yp
    have hleft' : componentAverage P.component (jointPoint x (dualCoordinates E M b)) =
        (n : ℝ)⁻¹ * ∑ i, ConeValue.component R q w i xp.fst xp.snd b := by
      rw [hPc]
      simpa only [xp, LinearIsometryEquiv.apply_symm_apply] using hleft
    have hright' : componentAverage P.component (jointPoint x y) =
        (n : ℝ)⁻¹ * ∑ i, ConeValue.component R q w i xp.fst xp.snd yp := by
      rw [hPc]
      simpa only [xp, yp, LinearIsometryEquiv.apply_symm_apply] using hright
    rw [hleft', hright'] at hh
    exact hh

/-- An arbitrary stationary output lies close to every recovered source in
its original output coordinates. The true proximal point is used only as an
analytic witness and is never treated as an oracle query. -/
theorem stationary_output_source_distance (hn : 0 < n) (L : ℝ) (hL : 0 < L)
    (R : ℝ) (hR : 0 < R) (q : ℝ) (hq : 16 ≤ q)
    (w : Fin n → Fin (M + 1) → E) (hw : ∀ j, Orthonormal ℝ (fun i ↦ w i j))
    (hAS : (problem hn L hL R hR q (by linarith) w hw).averagedSmooth)
    (c : PrimalSpace (primalDimension E M))
    (hc : StationaryOutput (problem hn L hL R hR q (by linarith) w hw) c) :
    ∀ j, ‖((primalCoordinates E M).symm c).fst j - sourceMean w j‖ ≤ (1 / 1000) / (2 * L) := by
  let P := problem hn L hL R hR q (by linarith) w hw
  let p := proximalMap hL (P.primal_continuous hAS) P.value_bddBelow c
  have hwitness := stationaryOutput_proximal_witness P hAS c hc
  change ∃ y ∈ (dualDomain E M R hR).carrier,
    componentAverage P.component (jointPoint p y) = primalObjective (dualDomain E M R hR) P.component p ∧
      ‖Accelerated.primalMeanGradient P p y‖ ≤ 1 / 1000 ∧ ‖p - c‖ ≤ (1 / 1000) / (2 * L) at hwitness
  obtain ⟨y, hy, hmax, hsmall, hdist⟩ := hwitness
  have hsource := actual_problem_source_recovery hn L hL R hR q hq w hw _ y hy hmax hsmall
  intro j
  have h1 := PiLp.norm_apply_le (p := 2)
    (((primalCoordinates E M).symm c).fst - ((primalCoordinates E M).symm p).fst) j
  have h2 := WithLp.norm_fst_le (p := 2) (α := Blocks E M) (β := Blocks E M)
    ((primalCoordinates E M).symm c - (primalCoordinates E M).symm p)
  have he : ‖(primalCoordinates E M).symm c - (primalCoordinates E M).symm p‖ = ‖c - p‖ := by
    rw [← map_sub, LinearIsometryEquiv.norm_map]
  rw [he] at h2
  have hs : ((primalCoordinates E M).symm p).fst j = sourceMean w j := hsource j
  rw [PiLp.sub_apply, hs] at h1
  have hd : ‖c - p‖ ≤ (1 / 1000) / (2 * L) := by
    rw [norm_sub_rev]
    exact hdist
  exact h1.trans (h2.trans hd)

end NCConcave16991.ConeProblem
