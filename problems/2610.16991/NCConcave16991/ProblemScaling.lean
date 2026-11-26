import NCConcave16991.DualRegularization
import NCConcave16991.TheoremStatements

/-! # Positive value and spatial scaling of actual finite-sum Problems -/

noncomputable section

open Set
open scoped BigOperators InnerProductSpace

namespace NCConcave16991.ProblemScaling

abbrev parameters (p : ProblemParameters) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ProblemParameters where
  n := p.n
  n_pos := p.n_pos
  L := a * b ^ 2 * p.L
  L_pos := mul_pos (mul_pos ha (sq_pos_of_pos hb)) p.L_pos
  gap := a * p.gap
  gap_pos := mul_pos ha p.gap_pos
  epsilon := a * b * p.epsilon
  epsilon_pos := mul_pos (mul_pos ha hb) p.epsilon_pos
  diameter := p.diameter / b
  diameter_nonneg := div_nonneg p.diameter_nonneg hb.le

def dualDomain {dy : ℕ} {D : ℝ} (K : KnownDualDomain dy D) (b : ℝ) (hb : 0 < b) :
    KnownDualDomain dy (D / b) where
  carrier := (fun y ↦ b • y) ⁻¹' K.carrier
  nonempty := by
    obtain ⟨y, hy⟩ := K.nonempty
    refine ⟨b⁻¹ • y, ?_⟩
    simpa only [mem_preimage, smul_smul, mul_inv_cancel₀ hb.ne', one_smul] using hy
  compact := by
    have he : (fun y ↦ b • y) ⁻¹' K.carrier = (fun y ↦ b⁻¹ • y) '' K.carrier := by
      ext y
      constructor
      · intro hy
        exact ⟨b • y, hy, by simp only [smul_smul, inv_mul_cancel₀ hb.ne', one_smul]⟩
      · rintro ⟨y, hy, rfl⟩
        simpa only [mem_preimage, smul_smul, mul_inv_cancel₀ hb.ne', one_smul] using hy
    rw [he]
    exact K.compact.image (continuous_const_smul _)
  convex := K.convex.linear_preimage (b • LinearMap.id)
  diameter_bound := by
    intro y hy z hz
    have h := K.diameter_bound (b • y) hy (b • z) hz
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hb] at h
    apply (le_div_iff₀ hb).2
    nlinarith only [h]

variable {p : ProblemParameters} {dx dy : ℕ} {K : KnownDualDomain dy p.diameter}
  {a b : ℝ} {ha : 0 < a} {hb : 0 < b}

def components (P : Problem p dx dy K) (a b : ℝ) (i : Fin p.n) (z : JointSpace dx dy) : ℝ :=
  a * P.component i (b • z)

def gradients (P : Problem p dx dy K) (a b : ℝ) (i : Fin p.n) (z : JointSpace dx dy) : JointSpace dx dy :=
  (a * b) • P.componentGradient i (b • z)

theorem average_components (P : Problem p dx dy K) (a b : ℝ) (z : JointSpace dx dy) :
    componentAverage (components P a b) z = a * componentAverage P.component (b • z) := by
  simp only [componentAverage, components, ← Finset.mul_sum]
  ring

theorem primal_value (P : Problem p dx dy K) (ha : 0 < a) (hb : 0 < b) (x : PrimalSpace dx) :
    primalObjective (dualDomain K b hb) (components P a b) x =
      a * primalObjective K P.component (b • x) := by
  have hupper (y : DualSpace dy) (hy : y ∈ (dualDomain K b hb).carrier) :
      componentAverage (components P a b) (jointPoint x y) ≤
        a * primalObjective K P.component (b • x) := by
    rw [average_components]
    exact mul_le_mul_of_nonneg_left (componentAverage_le_primalObjective P (b • x) (b • y) hy) ha.le
  obtain ⟨y, hy, hmax⟩ := P.exists_dual_maximizer (b • x)
  apply le_antisymm
  · apply csSup_le ((dualDomain K b hb).nonempty.image _)
    rintro v ⟨y, hy, rfl⟩
    exact hupper y hy
  · apply le_csSup
    · refine ⟨a * primalObjective K P.component (b • x), ?_⟩
      rintro v ⟨y, hy, rfl⟩
      exact hupper y hy
    · refine ⟨b⁻¹ • y, ?_, ?_⟩
      · change b • (b⁻¹ • y) ∈ K.carrier
        simpa only [smul_smul, mul_inv_cancel₀ hb.ne', one_smul] using hy
      · change componentAverage (components P a b) (jointPoint x (b⁻¹ • y)) = _
        rw [average_components, hmax]
        congr 2
        apply WithLp.ofLp_injective
        simp [jointPoint, smul_smul, hb.ne']

def toProblem (P : Problem p dx dy K) (ha : 0 < a) (hb : 0 < b) :
    Problem (parameters p a b ha hb) dx dy (dualDomain K b hb) where
  component := components (p := p) P a b
  componentGradient := gradients (p := p) P a b
  neighborhood := (fun z ↦ b • z) ⁻¹' P.neighborhood
  neighborhood_open := P.neighborhood_open.preimage (continuous_const_smul _)
  domain_subset := by
    intro z hz
    exact P.domain_subset (show b • z ∈ productDomain dx K from hz)
  gradient_correct := by
    intro i z hz
    rw [hasGradientAt_iff_hasFDerivAt]
    have h := ((P.gradient_correct i (b • z) hz).hasFDerivAt.comp z
      ((hasFDerivAt_id z).const_smul b)).const_smul a
    convert h using 1
    · rfl
    · ext w
      simp [gradients, real_inner_smul_left, inner_smul_right]
      ring
  average_dual_concave := by
    intro x
    refine ⟨(dualDomain K b hb).convex, ?_⟩
    intro y hy y' hy' c d hc hd hcd
    have h := (P.average_dual_concave (b • x)).2 hy hy' hc hd hcd
    have he : b • (c • y + d • y') = c • (b • y) + d • (b • y') := by module
    simp only [average_components, smul_eq_mul] at h ⊢
    change c * (a * componentAverage P.component (jointPoint (b • x) (b • y))) +
      d * (a * componentAverage P.component (jointPoint (b • x) (b • y'))) ≤
      a * componentAverage P.component (jointPoint (b • x) (b • (c • y + d • y')))
    rw [he]
    nlinarith only [mul_le_mul_of_nonneg_left h ha.le]
  initialPoint := b⁻¹ • P.initialPoint
  value_bddBelow := by
    obtain ⟨m, hm⟩ := P.value_bddBelow
    refine ⟨a * m, ?_⟩
    rintro v ⟨x, rfl⟩
    rw [primal_value P ha hb]
    exact mul_le_mul_of_nonneg_left (hm (mem_range_self (b • x))) ha.le
  initial_gap := by
    have hlo : a * sInf (range (primalObjective K P.component)) ≤
        sInf (range (primalObjective (dualDomain K b hb) (components P a b))) := by
      apply le_csInf (range_nonempty _)
      rintro v ⟨x, rfl⟩
      rw [primal_value P ha hb]
      exact mul_le_mul_of_nonneg_left (csInf_le P.value_bddBelow (mem_range_self (b • x))) ha.le
    rw [primal_value P ha hb]
    simp only [smul_smul, mul_inv_cancel₀ hb.ne', one_smul]
    have hg := mul_le_mul_of_nonneg_left P.initial_gap ha.le
    change a * primalObjective K P.component P.initialPoint - _ ≤ a * p.gap
    nlinarith only [hlo, hg]

theorem toProblem_individualSmooth (P : Problem p dx dy K) (ha : 0 < a) (hb : 0 < b)
    (hP : P.individualSmooth) : (toProblem P ha hb).individualSmooth := by
  intro i z hz w hw
  have h := hP i (b • z) hz (b • w) hw
  change ‖(a * b) • P.componentGradient i (b • z) -
      (a * b) • P.componentGradient i (b • w)‖ ≤ a * b ^ 2 * p.L * ‖z - w‖
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (mul_pos ha hb)]
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hb] at h
  have hh := mul_le_mul_of_nonneg_left h (mul_pos ha hb).le
  nlinarith only [hh]

theorem dimensionlessA_invariant (p : ProblemParameters) (ha : 0 < a) (hb : 0 < b) :
    dimensionlessA (parameters p a b ha hb) = dimensionlessA p := by
  unfold dimensionlessA parameters
  field_simp
  <;> ring

theorem dimensionlessB_invariant (p : ProblemParameters) (ha : 0 < a) (hb : 0 < b) :
    dimensionlessB (parameters p a b ha hb) = dimensionlessB p := by
  unfold dimensionlessB parameters
  field_simp
  <;> ring

end NCConcave16991.ProblemScaling
