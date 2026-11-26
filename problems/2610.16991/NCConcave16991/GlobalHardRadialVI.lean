import NCConcave16991.GlobalHardDual
import NCConcave16991.BranchConstructionConnectorVI

/-! # Direct radial coercivity at an actual constrained dual maximizer -/

noncomputable section

open Set
open scoped BigOperators InnerProductSpace

namespace NCConcave16991.GlobalHard

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {M N : ℕ} (V : Fin M → Fin (N + 1) → Type*)
  [∀ j k, NormedAddCommGroup (V j k)] [∀ j k, InnerProductSpace ℝ (V j k)]
  [∀ j k, CompleteSpace (V j k)]
variable (B : ∀ j : Fin M, ∀ t : Fin N,
  BranchGeometry.BranchFamily (ι := ι) (V j t.castSucc) (V j t.succ))
  (u : ∀ j, V j 0) (v : ∀ j, V j (Fin.last N))

theorem dualEdgeEnergy_smul (t : ℝ) (w : Dual V) :
    dualEdgeEnergy V B (t • w) = t ^ 2 * dualEdgeEnergy V B w := by
  simp only [dualEdgeEnergy, map_smul, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    ← Finset.mul_sum]

theorem average_dual_ray (d r μ : ℝ) (x : Primal V) (w : Dual V) (t : ℝ) :
    average V B u v d r μ (atDual V x (t • w)) =
      average V B u v d r μ (atDual V x 0) + t * dualLinear V r x w -
        t ^ 2 * (BranchGeometry.beta ι * (μ * ‖w‖ ^ 2 + dualEdgeEnergy V B w)) / 2 := by
  rw [average_dual_normal_form]
  simp only [map_smul, smul_eq_mul, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    dualEdgeEnergy_smul]
  ring

/-- The hypothesis is literal maximality along the feasible segment [0,w].
It follows for every maximizing point on any convex dual set containing zero. -/
theorem maximizing_dual_radial_coercivity (d r μ : ℝ) (x : Primal V) (w : Dual V)
    (hmax : ∀ t ∈ Icc (0 : ℝ) 1,
      average V B u v d r μ (atDual V x (t • w)) ≤ average V B u v d r μ (atDual V x w)) :
    BranchGeometry.beta ι * (μ * ‖w‖ ^ 2 + dualEdgeEnergy V B w) ≤ dualLinear V r x w := by
  let c := average V B u v d r μ (atDual V x 0)
  let l := dualLinear V r x w
  let E := BranchGeometry.beta ι * (μ * ‖w‖ ^ 2 + dualEdgeEnergy V B w)
  let f : ℝ → ℝ := fun t ↦ c + t * l - t ^ 2 * E / 2
  have hder : HasDerivAt f (l - E) 1 := by
    convert ((hasDerivAt_const (1 : ℝ) c).add ((hasDerivAt_id 1).mul_const l)).sub
      (((hasDerivAt_id 1).pow 2).mul_const (E / 2)) using 1
    · funext t
      simp only [f, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, id_eq]
      ring
    · norm_num
      ring
  have hfm : IsMaxOn f (Icc (0 : ℝ) 1) 1 := by
    intro t ht
    have hh := hmax t ht
    have h1 := average_dual_ray V B u v d r μ x w 1
    simp only [one_smul] at h1
    rw [average_dual_ray, h1] at hh
    simpa only [f, c, l, E, Set.mem_setOf_eq] using hh
  have hh := maximizer_hasGradientAt_vi (convex_Icc (0 : ℝ) 1)
    (show (1 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num) hfm hder.hasGradientAt
    0 (show (0 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
  simp only [RCLike.conj_to_real, zero_sub] at hh
  rw [Real.inner_apply] at hh
  change E ≤ l
  linarith

theorem maximizing_dual_radial_coercivity_on (d r μ : ℝ) (x : Primal V)
    {K : Set (Dual V)} (hK : Convex ℝ K) (hzero : 0 ∈ K) (w : Dual V) (hw : w ∈ K)
    (hmax : IsMaxOn (fun z ↦ average V B u v d r μ (atDual V x z)) K w) :
    BranchGeometry.beta ι * (μ * ‖w‖ ^ 2 + dualEdgeEnergy V B w) ≤ dualLinear V r x w := by
  apply maximizing_dual_radial_coercivity V B u v d r μ x w
  intro t ht
  apply hmax
  have hh := hK hzero hw (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel 1 t)
  simpa only [smul_zero, zero_add] using hh

end NCConcave16991.GlobalHard
