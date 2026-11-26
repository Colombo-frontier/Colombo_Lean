import NCConcave16991.ProblemAnalysis
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Concrete dual regularization from Appendix B

The functions here are computed from actual `Problem` components. The maximum,
uniform value perturbation, and Moreau-gradient perturbation are proved; they
are not supplied as interface hypotheses.
-/

open Set InnerProductSpace
open scoped InnerProductSpace BigOperators

namespace NCConcave16991

noncomputable section

variable {p : ProblemParameters} {dx dy : ℕ} {K : KnownDualDomain dy p.diameter}

def dualRegularizedComponent (P : Problem p dx dy K) (μ : ℝ) (y0 : DualSpace dy)
    (i : Fin p.n) (z : JointSpace dx dy) : ℝ :=
  P.component i z - μ / 2 * ‖z.snd - y0‖ ^ 2

def dualRegularizedGradient (P : Problem p dx dy K) (μ : ℝ) (y0 : DualSpace dy)
    (i : Fin p.n) (z : JointSpace dx dy) : JointSpace dx dy :=
  P.componentGradient i z - jointPoint 0 (μ • (z.snd - y0))

def dualRegularizedSection (P : Problem p dx dy K) (μ : ℝ) (y0 : DualSpace dy)
    (x : PrimalSpace dx) (y : DualSpace dy) : ℝ :=
  componentAverage P.component (jointPoint x y) - μ / 2 * ‖y - y0‖ ^ 2

/-- The actual regularized maximum `Psi`. -/
def dualRegularizedValue (P : Problem p dx dy K) (μ : ℝ) (y0 : DualSpace dy)
    (x : PrimalSpace dx) : ℝ :=
  sSup ((dualRegularizedSection P μ y0 x) '' K.carrier)

theorem dualPenalty_hasGradientAt (μ : ℝ) (y0 : DualSpace dy) (z : JointSpace dx dy) :
    HasGradientAt (fun u : JointSpace dx dy => μ / 2 * ‖u.snd - y0‖ ^ 2)
      (jointPoint 0 (μ • (z.snd - y0))) z := by
  rw [hasGradientAt_iff_hasFDerivAt]
  let S := WithLp.sndL 2 ℝ (PrimalSpace dx) (DualSpace dy)
  have hS : HasFDerivAt (fun u : JointSpace dx dy => u.snd - y0) S z :=
    S.hasFDerivAt.sub_const y0
  have hp := hS.norm_sq.const_smul (μ / 2)
  have hlin : toDual ℝ (JointSpace dx dy) (jointPoint 0 (μ • (z.snd - y0))) =
      (μ / 2) • ((2 : ℝ) • (innerSL ℝ (z.snd - y0)).comp S) := by
    ext w
    change ⟪jointPoint 0 (μ • (z.snd - y0)), w⟫_ℝ =
      μ / 2 * (2 * ⟪z.snd - y0, w.snd⟫_ℝ)
    simp [jointPoint, WithLp.prod_inner_apply, real_inner_smul_left]
    ring
  rw [hlin]
  convert hp using 1 <;> first
    | rfl
    | simp only [← Nat.cast_smul_eq_nsmul ℝ, Nat.cast_ofNat]

/-- The regularized gradient is proved to differentiate the regularized
component objective on its original open neighborhood. -/
theorem dualRegularizedComponent_hasGradientAt (P : Problem p dx dy K) (μ : ℝ)
    (y0 : DualSpace dy) (i : Fin p.n) (z : JointSpace dx dy) (hz : z ∈ P.neighborhood) :
    HasGradientAt (dualRegularizedComponent P μ y0 i)
      (dualRegularizedGradient P μ y0 i z) z := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hd := (P.gradient_correct i z hz).hasFDerivAt.sub
    (dualPenalty_hasGradientAt μ y0 z).hasFDerivAt
  convert hd using 1 <;> first
    | rfl
    | simp [dualRegularizedComponent, dualRegularizedGradient, map_sub]

/-- Concrete common dual regularization preserves AS with constant `L+μ`.
No bound on the constant affine term `μ y0` is required. -/
theorem dualRegularizedGradient_averagedSmooth (P : Problem p dx dy K)
    (hAS : P.averagedSmooth) {μ : ℝ} (hμ : 0 ≤ μ) (y0 : DualSpace dy) :
    AveragedSmooth (dualRegularizedGradient P μ y0) (productDomain dx K) (p.L + μ) := by
  let R : JointSpace dx dy → JointSpace dx dy := fun z => jointPoint 0 ((-μ) • z.snd)
  let b0 : JointSpace dx dy := jointPoint 0 (μ • y0)
  have hR : ∀ z ∈ productDomain dx K, ∀ z' ∈ productDomain dx K,
      ‖R z - R z'‖ ≤ μ * ‖z - z'‖ := by
    intro z hz z' hz'
    have he : R z - R z' = jointPoint 0 ((-μ) • (z.snd - z'.snd)) := by
      apply WithLp.ofLp_injective
      dsimp [R, jointPoint]
      simp only [WithLp.ofLp_sub, WithLp.ofLp_toLp, Prod.mk_sub_mk, sub_self, smul_sub]
    rw [he]
    change ‖WithLp.toLp 2 ((0 : PrimalSpace dx), (-μ) • (z.snd - z'.snd))‖ ≤ μ * ‖z - z'‖
    rw [WithLp.norm_toLp_snd, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hμ]
    apply mul_le_mul_of_nonneg_left _ hμ
    simpa only [WithLp.sub_snd] using WithLp.norm_snd_le
      (p := 2) (α := PrimalSpace dx) (β := DualSpace dy) (z - z')
  have hreg := AveragedSmooth.regularize p.n_pos (R := R) b0 p.L_pos.le hμ hAS hR
  have heq : (fun i z => P.componentGradient i z + R z + b0) = dualRegularizedGradient P μ y0 := by
    funext i z
    apply WithLp.ofLp_injective
    apply Prod.ext
    · change (P.componentGradient i z).fst + 0 + 0 = (P.componentGradient i z).fst - 0
      simp
    · change (P.componentGradient i z).snd + (-μ) • z.snd + μ • y0 =
        (P.componentGradient i z).snd - μ • (z.snd - y0)
      module
  rw [heq] at hreg
  exact hreg

theorem average_dualRegularizedComponent (P : Problem p dx dy K) (μ : ℝ)
    (y0 : DualSpace dy) (z : JointSpace dx dy) :
    componentAverage (dualRegularizedComponent P μ y0) z =
      componentAverage P.component z - μ / 2 * ‖z.snd - y0‖ ^ 2 := by
  have hn : (p.n : ℝ) ≠ 0 := by exact_mod_cast p.n_pos.ne'
  simp only [componentAverage, dualRegularizedComponent, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp [hn]

theorem dualRegularizedSection_continuousOn (P : Problem p dx dy K) (μ : ℝ)
    (y0 : DualSpace dy) (x : PrimalSpace dx) :
    ContinuousOn (dualRegularizedSection P μ y0 x) K.carrier := by
  have hq : Continuous (fun y : DualSpace dy => μ / 2 * ‖y - y0‖ ^ 2) :=
    continuous_const.mul ((continuous_id.sub continuous_const).norm.pow 2)
  exact (P.average_dual_continuous x).sub hq.continuousOn

/-- The actual average dual objective becomes `μ`-strongly concave. -/
theorem dualRegularizedSection_stronglyConcave (P : Problem p dx dy K) (μ : ℝ)
    (y0 : DualSpace dy) (x : PrimalSpace dx) :
    StrongConcaveOn K.carrier μ (dualRegularizedSection P μ y0 x) := by
  rw [strongConcaveOn_iff_convex]
  have ha : ConcaveOn ℝ K.carrier
      (fun y => μ * ⟪y, y0⟫_ℝ - μ / 2 * ‖y0‖ ^ 2) := by
    refine ⟨K.convex, ?_⟩
    intro y hy y' hy' a b ha hb hab
    simp only [inner_add_left, real_inner_smul_left, smul_eq_mul]
    apply le_of_eq
    rw [show b = 1 - a by linarith]
    ring
  convert (P.average_dual_concave x).add ha using 1
  ext y
  simp only [dualRegularizedSection, Pi.add_apply, norm_sub_sq_real]
  ring

theorem dualRegularizedValue_bddAbove (P : Problem p dx dy K) (μ : ℝ)
    (y0 : DualSpace dy) (x : PrimalSpace dx) :
    BddAbove ((dualRegularizedSection P μ y0 x) '' K.carrier) := by
  obtain ⟨y, hy, hmax⟩ := K.compact.exists_isMaxOn K.nonempty
    (dualRegularizedSection_continuousOn P μ y0 x)
  refine ⟨dualRegularizedSection P μ y0 x y, ?_⟩
  rintro v ⟨y', hy', rfl⟩
  exact hmax hy'

theorem dualRegularizedSection_le_value (P : Problem p dx dy K) (μ : ℝ)
    (y0 : DualSpace dy) (x : PrimalSpace dx) (y : DualSpace dy) (hy : y ∈ K.carrier) :
    dualRegularizedSection P μ y0 x y ≤ dualRegularizedValue P μ y0 x :=
  le_csSup (dualRegularizedValue_bddAbove P μ y0 x) ⟨y, hy, rfl⟩

theorem exists_dualRegularized_maximizer (P : Problem p dx dy K) (μ : ℝ)
    (y0 : DualSpace dy) (x : PrimalSpace dx) :
    ∃ y ∈ K.carrier, dualRegularizedValue P μ y0 x = dualRegularizedSection P μ y0 x y := by
  obtain ⟨y, hy, hmax⟩ := K.compact.exists_isMaxOn K.nonempty
    (dualRegularizedSection_continuousOn P μ y0 x)
  refine ⟨y, hy, le_antisymm ?_ (dualRegularizedSection_le_value P μ y0 x y hy)⟩
  apply csSup_le (K.nonempty.image _)
  rintro v ⟨y', hy', rfl⟩
  exact hmax hy'

theorem componentAverage_le_primalObjective (P : Problem p dx dy K)
    (x : PrimalSpace dx) (y : DualSpace dy) (hy : y ∈ K.carrier) :
    componentAverage P.component (jointPoint x y) ≤ primalObjective K P.component x := by
  have hb : BddAbove ((fun y => componentAverage P.component (jointPoint x y)) '' K.carrier) := by
    obtain ⟨y', hy', hmax⟩ := K.compact.exists_isMaxOn K.nonempty (P.average_dual_continuous x)
    refine ⟨componentAverage P.component (jointPoint x y'), ?_⟩
    rintro v ⟨y'', hy'', rfl⟩
    exact hmax hy''
  exact le_csSup hb ⟨y, hy, rfl⟩

/-- The diameter controls the actual uniform value perturbation. -/
theorem dualRegularizedValue_comparison (P : Problem p dx dy K) {μ : ℝ} (hμ : 0 ≤ μ)
    (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) (x : PrimalSpace dx) :
    0 ≤ primalObjective K P.component x - dualRegularizedValue P μ y0 x ∧
      primalObjective K P.component x - dualRegularizedValue P μ y0 x ≤ μ * p.diameter ^ 2 / 2 := by
  constructor
  · obtain ⟨y, hy, he⟩ := exists_dualRegularized_maximizer P μ y0 x
    have hbase := componentAverage_le_primalObjective P x y hy
    have hq : 0 ≤ μ / 2 * ‖y - y0‖ ^ 2 := by positivity
    rw [he]
    dsimp [dualRegularizedSection]
    linarith
  · obtain ⟨y, hy, he⟩ := P.exists_dual_maximizer x
    have hreg := dualRegularizedSection_le_value P μ y0 x y hy
    have hdiam := K.diameter_bound y hy y0 hy0
    have hsquare := pow_le_pow_left₀ (norm_nonneg _) hdiam 2
    have hq := mul_le_mul_of_nonneg_left hsquare (show 0 ≤ μ / 2 by positivity)
    dsimp [dualRegularizedSection] at hreg
    rw [he]
    nlinarith

theorem dualRegularizedValue_bddBelow (P : Problem p dx dy K) {μ : ℝ} (hμ : 0 ≤ μ)
    (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) :
    BddBelow (range (dualRegularizedValue P μ y0)) := by
  obtain ⟨m, hm⟩ := P.value_bddBelow
  refine ⟨m - μ * p.diameter ^ 2 / 2, ?_⟩
  rintro v ⟨x, rfl⟩
  have hbase := hm (mem_range_self x)
  have hgap := (dualRegularizedValue_comparison P hμ y0 hy0 x).2
  linarith

theorem dualRegularizedSection_hasGradientAt (P : Problem p dx dy K) (μ : ℝ)
    (y0 y : DualSpace dy) (hy : y ∈ K.carrier) (x : PrimalSpace dx) :
    HasGradientAt (fun u => dualRegularizedSection P μ y0 u y)
      (averageMap P.componentGradient (jointPoint x y)).fst x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  exact (P.hasGradientAt_primal_section x y hy).hasFDerivAt.sub_const (μ / 2 * ‖y - y0‖ ^ 2)

theorem dualRegularizedSection_weaklyConvex (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    (μ : ℝ) (y0 y : DualSpace dy) (hy : y ∈ K.carrier) :
    WeaklyConvex p.L (fun x => dualRegularizedSection P μ y0 x y) :=
  weaklyConvex_of_lipschitz_gradient p.L_pos.le
    (fun x => dualRegularizedSection_hasGradientAt P μ y0 y hy x)
    (P.primal_section_gradient_lipschitz hAS y hy)

theorem dualRegularizedValue_weaklyConvex (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    (μ : ℝ) (y0 : DualSpace dy) : WeaklyConvex p.L (dualRegularizedValue P μ y0) := by
  letI : Nonempty K.carrier := K.nonempty.to_subtype
  have hb (x : PrimalSpace dx) : BddAbove (range (fun y : K.carrier =>
      dualRegularizedSection P μ y0 x y)) := by
    rw [← image_eq_range]
    exact dualRegularizedValue_bddAbove P μ y0 x
  have hw := weaklyConvex_sSup
    (fun y : K.carrier => dualRegularizedSection_weaklyConvex P hAS μ y0 y y.property) hb
  have he : dualRegularizedValue P μ y0 = (fun x => sSup (range
      (fun y : K.carrier => dualRegularizedSection P μ y0 x y))) := by
    funext x
    unfold dualRegularizedValue
    rw [image_eq_range]
  rw [he]
  exact hw

theorem dualRegularizedValue_continuous (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    (μ : ℝ) (y0 : DualSpace dy) : Continuous (dualRegularizedValue P μ y0) := by
  have hw := dualRegularizedValue_weaklyConvex P hAS μ y0
  have hc : Continuous (fun x : PrimalSpace dx => dualRegularizedValue P μ y0 x + p.L / 2 * ‖x‖ ^ 2) :=
    continuousOn_univ.mp (ConvexOn.continuousOn isOpen_univ hw)
  have hq : Continuous (fun x : PrimalSpace dx => p.L / 2 * ‖x‖ ^ 2) :=
    continuous_const.mul (continuous_norm.pow 2)
  convert hc.sub hq using 1
  ext x
  dsimp
  ring

/-- The regularized envelope is the actual infimum-defined envelope at the
same parameter `1/(2L)` as the original envelope. -/
def dualRegularizedEnvelope (P : Problem p dx dy K) (μ : ℝ) (y0 : DualSpace dy) :=
  moreauEnvelope (dualRegularizedValue P μ y0) p.L

theorem dualRegularizedEnvelope_hasGradientAt (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    {μ : ℝ} (hμ : 0 ≤ μ) (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) (c : PrimalSpace dx) :
    HasGradientAt (dualRegularizedEnvelope P μ y0)
      ((2 * p.L) • (c - proximalMap p.L_pos (dualRegularizedValue_continuous P hAS μ y0)
        (dualRegularizedValue_bddBelow P hμ y0 hy0) c)) c :=
  moreauEnvelope_gradient_formula p.L_pos (dualRegularizedValue_continuous P hAS μ y0)
    (dualRegularizedValue_bddBelow P hμ y0 hy0) (dualRegularizedValue_weaklyConvex P hAS μ y0) c

/-- Appendix B's concrete squared Moreau-gradient error `2 L μ D_Y²`. -/
theorem dualRegularization_moreau_gradient_error (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    {μ : ℝ} (hμ : 0 ≤ μ) (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) (c : PrimalSpace dx) :
    ‖gradient (problemMoreauEnvelope P) c - gradient (dualRegularizedEnvelope P μ y0) c‖ ^ 2 ≤
      2 * p.L * μ * p.diameter ^ 2 := by
  have hphi := P.moreau_hasGradientAt hAS c
  have hpsi := dualRegularizedEnvelope_hasGradientAt P hAS hμ y0 hy0 c
  rw [hphi.gradient, hpsi.gradient]
  have hpert := proxResidual_perturbation p.L_pos.le (P.primal_weaklyConvex hAS)
    (dualRegularizedValue_weaklyConvex P hAS μ y0)
    (proximalMap_spec p.L_pos (P.primal_continuous hAS) P.value_bddBelow c)
    (proximalMap_spec p.L_pos (dualRegularizedValue_continuous P hAS μ y0)
      (dualRegularizedValue_bddBelow P hμ y0 hy0) c)
    (dualRegularizedValue_comparison P hμ y0 hy0)
  dsimp [proxResidual] at hpert
  nlinarith only [hpert]

/-- The explicit regularization parameter selected in Appendix B.1. -/
def selectedDualRegularization (p : ProblemParameters) : ℝ :=
  if p.diameter = 0 then p.L else
    min p.L (p.epsilon ^ 2 / (2 ^ 20 * p.L * p.diameter ^ 2))

theorem selectedDualRegularization_pos (p : ProblemParameters) :
    0 < selectedDualRegularization p := by
  unfold selectedDualRegularization
  split
  · exact p.L_pos
  · apply lt_min p.L_pos
    exact div_pos (sq_pos_of_pos p.epsilon_pos)
      (mul_pos (mul_pos (by norm_num) p.L_pos) (sq_pos_of_ne_zero ‹p.diameter ≠ 0›))

theorem selectedDualRegularization_le_L (p : ProblemParameters) :
    selectedDualRegularization p ≤ p.L := by
  unfold selectedDualRegularization
  split
  · exact le_rfl
  · exact min_le_left _ _

theorem selectedDualRegularization_value_error (p : ProblemParameters) :
    selectedDualRegularization p * p.diameter ^ 2 / 2 ≤
      p.epsilon ^ 2 / (2 ^ 21 * p.L) := by
  have hL := p.L_pos
  by_cases hD : p.diameter = 0
  · simp only [hD, zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_div]
    positivity
  · have hden : 0 < 2 ^ 20 * p.L * p.diameter ^ 2 :=
      mul_pos (mul_pos (by norm_num) p.L_pos) (sq_pos_of_ne_zero hD)
    have hμ : selectedDualRegularization p ≤ p.epsilon ^ 2 / (2 ^ 20 * p.L * p.diameter ^ 2) := by
      simp only [selectedDualRegularization, if_neg hD]
      exact min_le_right _ _
    have hm := (le_div_iff₀ hden).mp hμ
    apply (le_div_iff₀ (show 0 < 2 ^ 21 * p.L by positivity)).2
    norm_num at hm ⊢
    nlinarith only [hm]

/-- The fully instantiated transfer inequality in equation (B.1): neither the
uniform perturbation nor the Moreau-gradient error is assumed. -/
theorem selectedDualRegularization_transfer (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) (c : PrimalSpace dx) :
    (0 ≤ primalObjective K P.component c - dualRegularizedValue P (selectedDualRegularization p) y0 c ∧
      primalObjective K P.component c - dualRegularizedValue P (selectedDualRegularization p) y0 c ≤
        p.epsilon ^ 2 / (2 ^ 21 * p.L)) ∧
    ‖gradient (problemMoreauEnvelope P) c -
        gradient (dualRegularizedEnvelope P (selectedDualRegularization p) y0) c‖ ^ 2 ≤
      p.epsilon ^ 2 / 2 ^ 19 := by
  have hL := p.L_pos
  have hμ := (selectedDualRegularization_pos p).le
  have hgap := dualRegularizedValue_comparison P hμ y0 hy0 c
  have hr := selectedDualRegularization_value_error p
  constructor
  · exact ⟨hgap.1, hgap.2.trans hr⟩
  · have hg := dualRegularization_moreau_gradient_error P hAS hμ y0 hy0 c
    have hscaled := mul_le_mul_of_nonneg_left hr (show 0 ≤ 4 * p.L by positivity)
    have he : 4 * p.L * (p.epsilon ^ 2 / (2 ^ 21 * p.L)) = p.epsilon ^ 2 / 2 ^ 19 := by
      field_simp [p.L_pos.ne']
      ring
    rw [he] at hscaled
    nlinarith only [hg, hscaled]

end

end NCConcave16991
