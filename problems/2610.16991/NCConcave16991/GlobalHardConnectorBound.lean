import NCConcave16991.GlobalHardConnectorRay
import NCConcave16991.GlobalHardFrontier
import NCConcave16991.GlobalHardRadialVI

/-! # Actual connector control before proving dual interiority -/

namespace NCConcave16991.GlobalHard
noncomputable section
open Set LocalizationScalar LocalizationRadial
open scoped BigOperators InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048
set_option maxSynthPendingDepth 4
set_option maxHeartbeats 1000000

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {M N : ℕ} (V : Fin M → Fin (N + 1) → Type*)
  [∀ j k, NormedAddCommGroup (V j k)] [∀ j k, InnerProductSpace ℝ (V j k)]
  [∀ j k, CompleteSpace (V j k)]
variable (B : ∀ j : Fin M, ∀ t : Fin N,
    BranchGeometry.BranchFamily (ι := ι) (V j t.castSucc) (V j t.succ))
  (u : ∀ j, V j 0) (v : ∀ j, V j (Fin.last N))

theorem outerConnectorSumDerivative_abs_frontier (z : Joint V) (f : Fin M)
    (hu : ∀ j, ‖u j‖ = 1)
    (hhigh : ∀ j, j.val < f.val → 1 ≤ score V v j z)
    (hlow : ∀ j, f.val ≤ j.val → score V v j z ≤ 1 / 5)
    (hs : ‖stateProj V f z‖ ≤ 1 / 4) :
    |outerConnectorSumDerivative V u v z| ≤ 17 / 4 * ‖connectorTuple V z‖ := by
  unfold outerConnectorSumDerivative
  rw [Finset.sum_eq_single f]
  · have hh := outerConnectorDerivative_abs_bound (u f) (v f) (hu f)
      (precedingScore V v f z) (stateProj V f z) (aProj V f z) (bProj V f z) hs
    have hn : ‖WithLp.toLp 2 (aProj V f z, bProj V f z)‖ ≤ ‖connectorTuple V z‖ := by
      exact PiLp.norm_apply_le (p := 2) (connectorTuple V z) f
    exact hh.trans (mul_le_mul_of_nonneg_left hn (by norm_num))
  · intro j _ hj
    apply outerConnectorDerivative_zero
    rcases lt_or_gt_of_ne (show j.val ≠ f.val from fun h ↦ hj (Fin.ext h)) with h | h
    · exact activationLoad_zero_before_frontier V v z f hhigh j h
    · exact activationLoad_zero_after_frontier V v z f hlow j h
  · simp

theorem connectorRay_split (z : Joint V) (t : ℝ) :
    connectorRay V z t = WithLp.toLp 2
      (WithLp.fst z + (t - 1) • primalConnectorInjection V (connectorTuple V z), WithLp.snd z) := by
  apply WithLp.ofLp_injective 2
  change (WithLp.fst z + (t - 1) • primalConnectorInjection V (connectorTuple V z),
    WithLp.snd z + (t - 1) • 0) = _
  simp

theorem average_connector_derivative_abs_le (d r μ : ℝ) (z : Joint V) :
    |2 * d * ‖connectorTuple V z‖ ^ 2 + dualLinear V r (WithLp.fst z) (WithLp.snd z) +
      outerConnectorSumDerivative V u v z| ≤
      ‖gradient (primalAverageSection V B u v d r μ (WithLp.snd z)) (WithLp.fst z)‖ * ‖connectorTuple V z‖ := by
  let g := primalAverageSection V B u v d r μ (WithLp.snd z)
  let x := WithLp.fst z
  let h := primalConnectorInjection V (connectorTuple V z)
  have hg : HasGradientAt g (gradient g x) x :=
    ((primalAverageSection_contDiff V B u v d r μ (WithLp.snd z)).differentiable (by simp) x).hasGradientAt
  have hcurve : HasDerivAt (fun t : ℝ ↦ x + (t - 1) • h) h 1 := by
    convert ((((hasDerivAt_id (1 : ℝ)).sub_const 1).smul_const h).const_add x) using 1 <;> simp
  have hgg : HasFDerivAt g ((InnerProductSpace.toDual ℝ (Primal V)) (gradient g x)) (x + ((1 : ℝ) - 1) • h) := by
    simpa using hg.hasFDerivAt
  have hc := hgg.comp_hasDerivAt 1 hcurve
  have hc' : HasDerivAt (fun t : ℝ ↦ average V B u v d r μ (connectorRay V z t))
      ⟪gradient g x, h⟫_ℝ 1 := by
    convert hc using 1
    · funext t
      rw [connectorRay_split]
      rfl
    · simp only [InnerProductSpace.toDual_apply_apply]
  have heq := (average_connector_ray_hasDerivAt V B u v d r μ z).unique hc'
  rw [heq]
  have hh := abs_real_inner_le_norm (gradient g x) h
  simpa only [h, LinearIsometry.norm_map] using hh

theorem connector_norm_bound_of_frontier (d r μ : ℝ) (z : Joint V)
    (hd : 1 / 5 ≤ d) (hμ : 0 ≤ μ) (hu : ∀ j, ‖u j‖ = 1)
    (hv : ∀ j, ‖v j‖ = 1)
    (hg : ‖gradient (primalAverageSection V B u v d r μ (WithLp.snd z)) (WithLp.fst z)‖ ≤ 1 / 20)
    (f : Fin M) (hhigh : ∀ j, j.val < f.val → 1 ≤ score V v j z)
    (hlow : ∀ j, f.val ≤ j.val → -1 / 10 < score V v j z ∧ score V v j z ≤ 1 / 5)
    {K : Set (Dual V)} (hK : Convex ℝ K) (hzero : 0 ∈ K) (hw : WithLp.snd z ∈ K)
    (hmax : IsMaxOn (fun w ↦ average V B u v d r μ (atDual V (WithLp.fst z) w)) K (WithLp.snd z)) :
    ‖connectorTuple V z‖ ≤ 43 / 4 := by
  have hs := average_low_state_norm V B u v d r μ z hu hv hg f (hlow f le_rfl).1 (hlow f le_rfl).2
  have ho := outerConnectorSumDerivative_abs_frontier V u v z f hu hhigh (fun j hj ↦ (hlow j hj).2) hs.le
  have hder := (average_connector_derivative_abs_le V B u v d r μ z).trans
    (mul_le_mul_of_nonneg_right hg (norm_nonneg _))
  have hdual := maximizing_dual_radial_coercivity_on V B u v d r μ (WithLp.fst z) hK hzero (WithLp.snd z) hw hmax
  have hE : 0 ≤ dualEdgeEnergy V B (WithLp.snd z) := by
    unfold dualEdgeEnergy
    exact Finset.sum_nonneg (fun j _ ↦ Finset.sum_nonneg (fun t _ ↦ sq_nonneg _))
  have hl : 0 ≤ dualLinear V r (WithLp.fst z) (WithLp.snd z) :=
    (mul_nonneg (BranchGeometry.beta_pos ι).le (add_nonneg (mul_nonneg hμ (sq_nonneg _)) hE)).trans hdual
  have hupper := (abs_le.mp hder).2
  have holower := (abs_le.mp ho).1
  have hd' := mul_le_mul_of_nonneg_right hd (sq_nonneg ‖connectorTuple V z‖)
  by_contra hn
  have hgt : 43 / 4 < ‖connectorTuple V z‖ := lt_of_not_ge hn
  have hp := mul_pos (sub_pos.mpr hgt) (by linarith : (0 : ℝ) < ‖connectorTuple V z‖)
  nlinarith

end
end NCConcave16991.GlobalHard
