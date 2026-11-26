import GradientHessian.LeafNumerical
import GradientHessian.InnerLemma

/-! The literal capped leaves all live on the same physical space. A leaf
index is a parameter of its coefficients, never a new coordinate. -/

noncomputable section
namespace GradientHessian.Leaf
open InnerCoordinates
open Filter Set
open scoped Topology InnerProductSpace

def numericalRadius : ℝ := Inner.innerConstant + 2
def capFactor : ℝ := numericalRadius + 2
def capRadius (m : ℕ) : ℝ := capFactor*m

theorem numericalRadius_pos : 0 < numericalRadius := by
  unfold numericalRadius
  linarith [Inner.innerConstant_pos]
theorem capFactor_gt_one : 1 < capFactor := by
  unfold capFactor
  linarith [numericalRadius_pos]
theorem capRadius_pos {m : ℕ} (hm : 1 ≤ m) : 0 < capRadius m := by
  have h : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  exact mul_pos (lt_trans zero_lt_one capFactor_gt_one) h
theorem numericalRadius_lt_capRadius {m : ℕ} (hm : 1 ≤ m) : numericalRadius < capRadius m := by
  have h : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hc : capFactor ≤ capFactor*m :=
    le_mul_of_one_le_right (lt_trans zero_lt_one capFactor_gt_one).le h
  unfold capRadius
  linarith [show capFactor = numericalRadius+2 from rfl]

variable {Y E : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {m : ℕ}

abbrev Space (Y E : Type*) [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (m : ℕ) :=
  InnerCoordinates.Space Y E m (Inner.absoluteDepth+2)

def publicQuadratic (m : ℕ) (Z : Space Y E m) : ℝ :=
  m*‖numerical Y E m (Inner.absoluteDepth+2) Z‖^2 + Inner.publicQuadratic m Inner.absoluteDepth Z

def correction (A : Y →L[ℝ] Y) (b a : Fin m → Y)
    (v : Fin m → Fin (Inner.absoluteDepth+2) → E) (Z : Space Y E m) : ℝ :=
  LeafCorrection.correction (capRadius m) (LeafNumerical.deviation m A)
    (numerical Y E m (Inner.absoluteDepth+2) Z) + Inner.residual b a v Z

def objective (A : Y →L[ℝ] Y) (b a : Fin m → Y)
    (v : Fin m → Fin (Inner.absoluteDepth+2) → E) (Z : Space Y E m) : ℝ :=
  publicQuadratic m Z + correction A b a v Z

def outgoing (v : Fin (m+1) → Fin (Inner.absoluteDepth+2) → E) (Z : Space Y E (m+1)) : ℝ :=
  Inner.outgoing v Z

def driven (A : Y →L[ℝ] Y) (b a : Fin (m+1) → Y)
    (v : Fin (m+1) → Fin (Inner.absoluteDepth+2) → E) (l : ℝ) (Z : Space Y E (m+1)) : ℝ :=
  objective A b a v Z - l*outgoing v Z

theorem objective_decomposition (A : Y →L[ℝ] Y) (b a : Fin m → Y)
    (v : Fin m → Fin (Inner.absoluteDepth+2) → E) (Z : Space Y E m) :
    objective A b a v Z = LeafNumerical.base m (capRadius m) A
      (numerical Y E m (Inner.absoluteDepth+2) Z) +
        Inner.publicQuadratic m Inner.absoluteDepth Z + Inner.residual b a v Z := by
  unfold objective publicQuadratic correction LeafNumerical.base
  ring

theorem publicQuadratic_contDiff (m : ℕ) :
    ContDiff ℝ 3 (publicQuadratic (Y := Y) (E := E) m) :=
  (contDiff_const.mul ((numerical Y E m (Inner.absoluteDepth+2)).contDiff.norm_sq ℝ)).add
    (Inner.publicQuadratic_contDiff m Inner.absoluteDepth)

theorem correction_contDiff (hm : 1 ≤ m) (A : Y →L[ℝ] Y) (b a : Fin m → Y)
    (v : Fin m → Fin (Inner.absoluteDepth+2) → E) : ContDiff ℝ 3 (correction A b a v) :=
  ((LeafCorrection.correction_contDiff (capRadius_pos hm) _).comp
    (numerical Y E m (Inner.absoluteDepth+2)).contDiff).add (Inner.residual_contDiff b a v)

theorem objective_contDiff (hm : 1 ≤ m) (A : Y →L[ℝ] Y) (b a : Fin m → Y)
    (v : Fin m → Fin (Inner.absoluteDepth+2) → E) : ContDiff ℝ 3 (objective A b a v) :=
  (publicQuadratic_contDiff m).add (correction_contDiff hm A b a v)

theorem driven_contDiff (A : Y →L[ℝ] Y) (b a : Fin (m+1) → Y)
    (v : Fin (m+1) → Fin (Inner.absoluteDepth+2) → E) (l : ℝ) :
    ContDiff ℝ 3 (driven A b a v l) :=
  (objective_contDiff (by omega) A b a v).sub
    (contDiff_const.mul (Inner.ports_contDiff v (Fin.last m)))

theorem correction_nonpos (A : Y →L[ℝ] Y) (hA : ‖A‖ ≤ m) (b a : Fin m → Y)
    (v : Fin m → Fin (Inner.absoluteDepth+2) → E) (Z : Space Y E m) :
    correction A b a v Z ≤ 0 := by
  have hC := LeafNumerical.deviation_nonpos (Nat.cast_nonneg m) A hA
    (numerical Y E m (Inner.absoluteDepth+2) Z)
  have hθ := (LeafCutoff.cutoff_bounds (capRadius m)
    (numerical Y E m (Inner.absoluteDepth+2) Z)).1
  have hW := (Inner.residual_bounds b a v Z).2
  unfold correction LeafCorrection.correction LeafCorrection.quadratic
  exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos (by positivity) hC) hW

theorem objective_energy (hm : 1 ≤ m) (A : Y →L[ℝ] Y) (hA : InverseGate.LowerBound A)
    (b a : Fin m → Y) (v : Fin m → Fin (Inner.absoluteDepth+2) → E) (Z : Space Y E m) :
    ‖numerical Y E m (Inner.absoluteDepth+2) Z‖^2/2 +
      Inner.publicQuadratic m Inner.absoluteDepth Z - Inner.innerConstant*m ≤ objective A b a v Z := by
  have hn := LeafNumerical.base_lower (show (1:ℝ) ≤ m by exact_mod_cast hm)
    (capRadius m) A hA (numerical Y E m (Inner.absoluteDepth+2) Z)
  have hW := (Inner.residual_bounds b a v Z).1
  have hC := mul_le_mul_of_nonneg_right Inner.innerConstant_value (Nat.cast_nonneg m)
  rw [objective_decomposition]
  linarith

theorem objective_eq_inner (hm : 1 ≤ m) (A : Y →L[ℝ] Y) (b a : Fin m → Y)
    (v : Fin m → Fin (Inner.absoluteDepth+2) → E) (Z : Space Y E m)
    (hZ : ‖numerical Y E m (Inner.absoluteDepth+2) Z‖ ≤ capRadius m) :
    objective A b a v Z = Inner.objective A b a v Z := by
  rw [objective_decomposition, Inner.objective_decomposition, LeafNumerical.base_mixture,
    LeafCutoff.cutoff_one (capRadius_pos hm) hZ]
  ring

theorem objective_eventually_eq_inner (hm : 1 ≤ m) (A : Y →L[ℝ] Y) (b a : Fin m → Y)
    (v : Fin m → Fin (Inner.absoluteDepth+2) → E) (Z : Space Y E m)
    (hZ : ‖numerical Y E m (Inner.absoluteDepth+2) Z‖ < capRadius m) :
    objective A b a v =ᶠ[𝓝 Z] Inner.objective A b a v := by
  have hn : ∀ᶠ W : Space Y E m in 𝓝 Z,
      ‖numerical Y E m (Inner.absoluteDepth+2) W‖ < capRadius m :=
    (numerical Y E m (Inner.absoluteDepth+2)).continuous.norm.continuousAt.eventually (gt_mem_nhds hZ)
  filter_upwards [hn] with W hW
  exact objective_eq_inner hm A b a v W hW.le

theorem bounded_correction (A : Y →L[ℝ] Y) (hA : ‖A‖ ≤ m) (b a : Fin m → Y)
    (v : Fin m → Fin (Inner.absoluteDepth+2) → E) (Z : Space Y E m)
    (hZ : ‖numerical Y E m (Inner.absoluteDepth+2) Z‖ ≤ numericalRadius) :
    -(2*numericalRadius^2+Inner.innerConstant)*m ≤ correction A b a v Z ∧
      correction A b a v Z ≤ 0 := by
  refine ⟨?_, correction_nonpos A hA b a v Z⟩
  let y := numerical Y E m (Inner.absoluteDepth+2) Z
  let C := LeafNumerical.deviation m A
  have hn : ‖C‖ ≤ 3*m := LeafNumerical.deviation_norm (Nat.cast_nonneg m) A hA
  have hq : |⟪y,C y⟫_ℝ| ≤ (3*m)*numericalRadius^2 := by
    calc
      _ ≤ ‖y‖*‖C y‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖y‖*(‖C‖*‖y‖) := mul_le_mul_of_nonneg_left (C.le_opNorm y) (norm_nonneg y)
      _ = ‖C‖*‖y‖^2 := by ring
      _ ≤ (3*m)*numericalRadius^2 := by gcongr
  have hθ := LeafCutoff.cutoff_bounds (capRadius m) y
  have hc : -(3*m)*numericalRadius^2 ≤ LeafCutoff.cutoff (capRadius m) y * ⟪y,C y⟫_ℝ := by
    have hab := mul_le_mul_of_nonneg_left hq hθ.1
    have hcap : LeafCutoff.cutoff (capRadius m) y*((3*m)*numericalRadius^2) ≤
        (3*m)*numericalRadius^2 := mul_le_of_le_one_left (by positivity) hθ.2
    have hlo := neg_abs_le ⟪y,C y⟫_ℝ
    have hm := mul_le_mul_of_nonneg_left hlo hθ.1
    nlinarith
  have hW := (Inner.residual_bounds b a v Z).1
  have hC := mul_le_mul_of_nonneg_right Inner.innerConstant_value (Nat.cast_nonneg m)
  change _ ≤ (1/2)*LeafCutoff.cutoff (capRadius m) y*⟪y,C y⟫_ℝ + Inner.residual b a v Z
  nlinarith [mul_nonneg (Nat.cast_nonneg m) (sq_nonneg numericalRadius)]

theorem inner_block_zero {k : ℕ} (v : Fin (k+2) → E) :
    Inner.block v 0 = 0 := by
  rw [Inner.block, LatchChain.self_eq_adjacent_sum]
  simp [LatchChain.atom, LatchChain.u, LatchActivation.readout, RadialSquash.squash_zero,
    Profiles.chi_zero (by norm_num : (0:ℝ) ≤ 1/4)]

theorem inner_ports_zero {k : ℕ} (v : Fin m → Fin (k+2) → E) (i : Fin m) :
    Inner.ports v (0 : InnerCoordinates.Space Y E m (k+2)) i = 0 := by
  simp [Inner.ports, Inner.completion, LatchChain.port, LatchChain.u,
    LatchActivation.readout, RadialSquash.squash_zero,
    Profiles.varpi_zero (by norm_num : (0:ℝ) ≤ 2/3)]

theorem inner_payload_zero {k : ℕ} (b a : Fin m → Y) (v : Fin m → Fin (k+2) → E)
    (i : Fin m) : Inner.payload b a v (0 : InnerCoordinates.Space Y E m (k+2)) i =
      10*InverseGate.H₀^2 := by
  simp [Inner.payload, InverseGate.forcing, InverseGate.forcingArg,
    InverseGate.gate, InverseGate.gateArg, RadialSquash.squash_zero,
    Profiles.chi_zero (by norm_num : (0:ℝ) ≤ 1/4),
    IntegralProfiles.theta_identity (by norm_num : |(0:ℝ)| ≤ 8), mul_comm]

theorem inner_forcingSum_zero {k : ℕ} (b a : Fin (m+1) → Y)
    (v : Fin (m+1) → Fin (k+2) → E) :
    Inner.forcingSum b a v (0 : InnerCoordinates.Space Y E (m+1) (k+2)) = 10*InverseGate.H₀^2 := by
  rw [Inner.forcingSum, InnerSelector.select]
  simp only [inner_ports_zero, inner_payload_zero, sub_zero, one_mul, zero_mul, add_zero]

theorem objective_zero (A : Y →L[ℝ] Y) (b a : Fin (m+1) → Y)
    (v : Fin (m+1) → Fin (Inner.absoluteDepth+2) → E) :
    objective A b a v (0 : Space Y E (m+1)) = -10*InverseGate.H₀^2 := by
  rw [objective_eq_inner (by omega) A b a v 0 (by simpa using (capRadius_pos (by omega : 1 ≤ m+1)).le)]
  simp [Inner.objective, InverseGate.quadratic, Inner.selfSum, inner_block_zero,
    inner_forcingSum_zero]

end GradientHessian.Leaf
