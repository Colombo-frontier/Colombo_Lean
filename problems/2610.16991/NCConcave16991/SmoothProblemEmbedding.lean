import NCConcave16991.ProblemAnalysis
import NCConcave16991.SmoothMoreau

/-!
# The literal smooth finite-sum embedding in Appendix F.1

An arbitrary globally differentiable individually smooth finite sum is
embedded as a genuine Problem independent of its singleton dual variable.
The exact value/full-gradient reply and the Moreau-to-direct-gradient
stationarity transfer are proved. No external lower bound is assumed here.
-/

open Set InnerProductSpace
open scoped BigOperators InnerProductSpace

namespace NCConcave16991

noncomputable section

def smoothSumAverage {n dx : ℕ} (f : Fin n → PrimalSpace dx → ℝ) (x : PrimalSpace dx) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, f i x

structure SmoothFiniteSum (p : ProblemParameters) (dx : ℕ) where
  component : Fin p.n → PrimalSpace dx → ℝ
  componentGradient : Fin p.n → PrimalSpace dx → PrimalSpace dx
  gradient_correct : ∀ i x, HasGradientAt (component i) (componentGradient i x) x
  individualSmooth : ∀ i x y, ‖componentGradient i x - componentGradient i y‖ ≤ p.L * ‖x - y‖
  initialPoint : PrimalSpace dx
  boundedBelow : BddBelow (range (smoothSumAverage component))
  initialGap : smoothSumAverage component initialPoint - sInf (range (smoothSumAverage component)) ≤ p.gap

def smoothDualDomain (p : ProblemParameters) : KnownDualDomain 0 p.diameter where
  carrier := {0}
  nonempty := ⟨0, mem_singleton 0⟩
  compact := isCompact_singleton
  convex := convex_singleton 0
  diameter_bound := by
    intro y hy y' hy'
    simp only [mem_singleton_iff] at hy hy'
    subst y
    subst y'
    simpa using p.diameter_nonneg

namespace SmoothFiniteSum

variable {p : ProblemParameters} {dx : ℕ}

def jointComponent (F : SmoothFiniteSum p dx) (i : Fin p.n) (z : JointSpace dx 0) : ℝ :=
  F.component i z.fst

def jointGradient (F : SmoothFiniteSum p dx) (i : Fin p.n) (z : JointSpace dx 0) : JointSpace dx 0 :=
  jointPoint (F.componentGradient i z.fst) 0

theorem jointComponent_hasGradientAt (F : SmoothFiniteSum p dx) (i : Fin p.n) (z : JointSpace dx 0) :
    HasGradientAt (F.jointComponent i) (F.jointGradient i z) z := by
  let S := WithLp.fstL 2 ℝ (PrimalSpace dx) (DualSpace 0)
  have hh := (F.gradient_correct i z.fst).hasFDerivAt.comp z S.hasFDerivAt
  rw [hasGradientAt_iff_hasFDerivAt]
  have he : toDual ℝ (JointSpace dx 0) (F.jointGradient i z) =
      (toDual ℝ (PrimalSpace dx) (F.componentGradient i z.fst)).comp S := by
    ext w
    simp [jointGradient, jointPoint, WithLp.prod_inner_apply, S]
  rw [he]
  exact hh

theorem joint_average (F : SmoothFiniteSum p dx) (x : PrimalSpace dx) (y : DualSpace 0) :
    componentAverage F.jointComponent (jointPoint x y) = smoothSumAverage F.component x := rfl

theorem primal_value (F : SmoothFiniteSum p dx) (x : PrimalSpace dx) :
    primalObjective (smoothDualDomain p) F.jointComponent x = smoothSumAverage F.component x := by
  change sSup ((fun y ↦ componentAverage F.jointComponent (jointPoint x y)) '' {0}) = _
  rw [image_singleton, csSup_singleton]
  rfl

def toProblem (F : SmoothFiniteSum p dx) : Problem p dx 0 (smoothDualDomain p) where
  component := F.jointComponent
  componentGradient := F.jointGradient
  neighborhood := univ
  neighborhood_open := isOpen_univ
  domain_subset := subset_univ _
  gradient_correct := fun i z _ ↦ F.jointComponent_hasGradientAt i z
  average_dual_concave := by
    intro x
    have he : (fun y ↦ componentAverage F.jointComponent (jointPoint x y)) =
        fun _ : DualSpace 0 ↦ smoothSumAverage F.component x := funext (F.joint_average x)
    rw [he]
    exact concaveOn_const _ (smoothDualDomain p).convex
  initialPoint := F.initialPoint
  value_bddBelow := by
    have he := funext F.primal_value
    rw [he]
    exact F.boundedBelow
  initial_gap := by
    have he := funext F.primal_value
    rw [he]
    exact F.initialGap

theorem toProblem_individualSmooth (F : SmoothFiniteSum p dx) : F.toProblem.individualSmooth := by
  intro i z hz w hw
  have he : ‖F.jointGradient i z - F.jointGradient i w‖ =
      ‖F.componentGradient i z.fst - F.componentGradient i w.fst‖ := by
    change ‖WithLp.toLp 2 (F.componentGradient i z.fst - F.componentGradient i w.fst,
      (0 : DualSpace 0) - 0)‖ = _
    rw [sub_self, WithLp.norm_toLp_fst]
  change ‖F.jointGradient i z - F.jointGradient i w‖ ≤ p.L * ‖z - w‖
  rw [he]
  exact (F.individualSmooth i z.fst w.fst).trans
    (mul_le_mul_of_nonneg_left
      (by simpa only [WithLp.sub_fst] using
        (WithLp.norm_fst_le (p := 2) (α := PrimalSpace dx) (β := DualSpace 0) (z - w))) p.L_pos.le)

theorem average_hasGradientAt (F : SmoothFiniteSum p dx) (x : PrimalSpace dx) :
    HasGradientAt (smoothSumAverage F.component) (averageMap F.componentGradient x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hh := HasFDerivAt.fun_sum (u := Finset.univ)
    (fun i _ ↦ (F.gradient_correct i x).hasFDerivAt)
  convert hh.const_smul ((p.n : ℝ)⁻¹) using 1
  · rfl
  · simp [averageMap, map_smul, map_sum]

theorem averageGradient_lipschitz (F : SmoothFiniteSum p dx) (x y : PrimalSpace dx) :
    ‖averageMap F.componentGradient x - averageMap F.componentGradient y‖ ≤ p.L * ‖x - y‖ := by
  have hIS : IndividualSmooth F.componentGradient univ p.L := fun i x _ y _ ↦ F.individualSmooth i x y
  have hAS := IndividualSmooth.averagedSmooth p.L_pos.le hIS
  exact AveragedSmooth.average_lipschitz p.n_pos p.L_pos.le hAS x (mem_univ x) y (mem_univ y)

theorem problemMoreau_eq (F : SmoothFiniteSum p dx) :
    problemMoreauEnvelope F.toProblem = moreauEnvelope (smoothSumAverage F.component) p.L := by
  have he := funext F.primal_value
  change moreauEnvelope (primalObjective (smoothDualDomain p) F.jointComponent) p.L = _
  rw [he]

theorem oracle_reply (F : SmoothFiniteSum p dx)
    (q : OracleQuery p.n dx (smoothDualDomain p)) :
    oracleResponse F.toProblem q =
      (F.component q.1 q.2.1, F.componentGradient q.1 q.2.1, (0 : DualSpace 0)) := rfl

/-- A successful output transfers without extra oracle queries or a gradient
verification pass, for every arbitrary output point. -/
theorem stationary_implies_direct_gradient (F : SmoothFiniteSum p dx) (x : PrimalSpace dx)
    (hx : StationaryOutput F.toProblem x) :
    ‖gradient (smoothSumAverage F.component) x‖ ≤ (3 / 2 : ℝ) * p.epsilon := by
  obtain ⟨g, hg, hn⟩ := hx
  rw [F.problemMoreau_eq] at hg
  have hh := (smooth_gradient_moreau_comparison p.L_pos F.average_hasGradientAt
    F.averageGradient_lipschitz F.boundedBelow x).2
  rw [hg.gradient] at hh
  nlinarith only [hh, hn]

end SmoothFiniteSum

end

end NCConcave16991
