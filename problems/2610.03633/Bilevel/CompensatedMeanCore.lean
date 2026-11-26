import Bilevel.CompensatedMeanSpace
import Bilevel.SmallGapLiftSupport
import Bilevel.ZeroChainCarry

/-! The actual globally clipped compensated mean objectives and their first
derivatives. The finite decomposition is retained exactly; the dummy block
has curvature L. Regularity budgets are proved in subsequent modules. -/

noncomputable section
namespace Bilevel.CompensatedMean
open scoped RealInnerProductSpace
open SmallGapProfiles SmallGapLiftSupport

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

structure Data where
  μ : ℝ
  L : ℝ
  J : ℕ
  r : E → ℝ
  A : E → ℝ
  e : ℕ → E → ℝ
  w : ℕ → ℝ
  r_smooth : ContDiff ℝ 3 r
  A_smooth : ContDiff ℝ 3 A
  e_smooth : ∀ j, ContDiff ℝ 3 (e j)
  w_pos : ∀ j, j ≤ J → 0 < w j
  decomposition : ∀ u, (∑ j ∈ Finset.range (J+1), e j u) = r u

namespace Data
variable (P : Data (E := E))

def perturbation (y : LowerSpace E) : ℝ :=
  P.μ/(2*P.L^2)*(P.r (uProj E y))^2 -
    P.μ/P.L*∑ j ∈ Finset.range (P.J+1), P.e j (uProj E y)*normal (P.w j) (sProj E y)

def upper (_x : E) (y : LowerSpace E) : ℝ := P.A (uProj E y)+P.L*sProj E y

def lower (x : E) (y : LowerSpace E) : ℝ :=
  P.μ/2*(‖uProj E y‖^2+(sProj E y)^2)+P.L/2*(zProj E y)^2-
    P.L*⟪x,uProj E y⟫+P.perturbation y

def perturbationU (y : LowerSpace E) : E :=
  (P.μ/P.L^2*P.r (uProj E y)) • gradient P.r (uProj E y)-
    (P.μ/P.L) • ∑ j ∈ Finset.range (P.J+1),
      normal (P.w j) (sProj E y) • gradient (P.e j) (uProj E y)

def perturbationS (y : LowerSpace E) : ℝ :=
  -(P.μ/P.L)*∑ j ∈ Finset.range (P.J+1),
    P.e j (uProj E y)*deriv (normal (P.w j)) (sProj E y)

def perturbationGradient (y : LowerSpace E) : LowerSpace E :=
  pack E (P.perturbationU y) (P.perturbationS y) 0

def upperX (_P : Data (E := E)) (_x : E) (_y : LowerSpace E) : E := 0
def upperY (_x : E) (y : LowerSpace E) : LowerSpace E :=
  pack E (gradient P.A (uProj E y)) P.L 0
def lowerX (_x : E) (y : LowerSpace E) : E := -P.L • uProj E y
def lowerY (x : E) (y : LowerSpace E) : LowerSpace E :=
  pack E (P.μ • uProj E y-P.L • x+P.perturbationU y)
    (P.μ*sProj E y+P.perturbationS y) (P.L*zProj E y)

omit [CompleteSpace E] in
theorem perturbation_contDiff : ContDiff ℝ 3 P.perturbation := by
  apply (contDiff_const.mul ((P.r_smooth.comp (uProj E).contDiff).pow 2)).sub
  apply contDiff_const.mul
  apply ContDiff.sum
  intro j hj
  exact ((P.e_smooth j).comp (uProj E).contDiff).mul
    ((normal_contDiff (P.w j) (P.w_pos j (by have := Finset.mem_range.mp hj; omega))).comp (sProj E).contDiff)

omit [CompleteSpace E] in
theorem upper_contDiff (x : E) : ContDiff ℝ 3 (P.upper x) :=
  (P.A_smooth.comp (uProj E).contDiff).add (contDiff_const.mul (sProj E).contDiff)

omit [CompleteSpace E] in
theorem lower_contDiff (x : E) : ContDiff ℝ 3 (P.lower x) := by
  have hu := (uProj E).contDiff (n := (3:WithTop ℕ∞))
  have hs := (sProj E).contDiff (n := (3:WithTop ℕ∞))
  have hz := (zProj E).contDiff (n := (3:WithTop ℕ∞))
  have hnorm : ContDiff ℝ 3 (fun y : LowerSpace E => ‖uProj E y‖^2) := by
    simpa only [real_inner_self_eq_norm_sq] using hu.inner ℝ hu
  exact (((contDiff_const.mul (hnorm.add (hs.pow 2))).add
    (contDiff_const.mul (hz.pow 2))).sub (contDiff_const.mul (contDiff_const.inner ℝ hu))).add
    P.perturbation_contDiff

theorem perturbation_hasGradientAt (y : LowerSpace E) :
    HasGradientAt P.perturbation (P.perturbationGradient y) y := by
  have hu := (uProj E).hasFDerivAt (x := y)
  have hs := (sProj E).hasFDerivAt (x := y)
  have hr := ((P.r_smooth.differentiable (by norm_num) _).hasGradientAt.hasFDerivAt).comp y hu
  have he (j : ℕ) := ((P.e_smooth j).differentiable (by norm_num) _).hasGradientAt.hasFDerivAt.comp y hu
  have hq (j : ℕ) (hj : j ∈ Finset.range (P.J+1)) :=
    ((normal_contDiff (P.w j) (P.w_pos j (by have := Finset.mem_range.mp hj; omega))).differentiable
      (by norm_num) (sProj E y)).hasDerivAt.hasFDerivAt.comp y hs
  have hsum := HasFDerivAt.sum (fun j hj => (he j).mul (hq j hj))
  have h := ((hr.mul hr).const_mul (P.μ/(2*P.L^2))).sub (hsum.const_mul (P.μ/P.L))
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert h using 1
  · ext v
    simp only [perturbation,pow_two,Function.comp_apply]
  ext v
  simp only [perturbationGradient,perturbationU,perturbationS,InnerProductSpace.toDual_apply,
    inner_pack,inner_sub_left,real_inner_smul_left,sum_inner,ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sum_apply,ContinuousLinearMap.mul_apply,ContinuousLinearMap.smulRight_apply,
    smul_eq_mul,zero_mul,add_zero,Function.comp_apply,ContinuousLinearMap.one_apply]
  simp only [Finset.sum_add_distrib,Finset.mul_sum,Finset.sum_mul,sum_inner,real_inner_smul_left]
  ring_nf
  simp only [Finset.mul_sum,Finset.sum_mul,← Finset.sum_neg_distrib]
  ring_nf

theorem upper_hasGradientX (x : E) (y : LowerSpace E) :
    HasGradientAt (fun x => P.upper x y) (P.upperX x y) x := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  simpa only [upperX,map_zero] using hasFDerivAt_const (P.upper x y) x

theorem upper_hasGradientY (x : E) (y : LowerSpace E) :
    HasGradientAt (P.upper x) (P.upperY x y) y := by
  have h := (((P.A_smooth.differentiable (by norm_num) _).hasGradientAt.hasFDerivAt).comp y
    ((uProj E).hasFDerivAt)).add (((sProj E).hasFDerivAt).const_mul P.L)
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert h using 1
  ext v
  simp only [upperY,InnerProductSpace.toDual_apply,inner_pack,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,zero_mul,add_zero]

theorem lower_hasGradientX (x : E) (y : LowerSpace E) :
    HasGradientAt (fun x => P.lower x y) (P.lowerX x y) x := by
  have h := ((hasFDerivAt_id x).inner ℝ (hasFDerivAt_const (uProj E y) x)).const_mul P.L
  have hh := (h.const_sub (P.μ/2*(‖uProj E y‖^2+(sProj E y)^2)+P.L/2*(zProj E y)^2)).add_const
    (P.perturbation y)
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert hh using 1
  ext v
  simp [lowerX,InnerProductSpace.toDual_apply,real_inner_smul_left,real_inner_comm]

theorem lower_hasGradientY (x : E) (y : LowerSpace E) :
    HasGradientAt (P.lower x) (P.lowerY x y) y := by
  have hu := (uProj E).hasFDerivAt (x := y)
  have hs := (sProj E).hasFDerivAt (x := y)
  have hz := (zProj E).hasFDerivAt (x := y)
  have h := (((((hu.inner ℝ hu).add (hs.mul hs)).const_mul (P.μ/2)).add
    ((hz.mul hz).const_mul (P.L/2))).sub
      (((hasFDerivAt_const x y).inner ℝ hu).const_mul P.L)).add (P.perturbation_hasGradientAt y).hasFDerivAt
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert h using 1
  · ext v
    simp only [lower,pow_two,real_inner_self_eq_norm_sq]
  ext v
  simp only [lowerY,perturbationGradient,InnerProductSpace.toDual_apply,inner_pack,
    inner_add_left,inner_sub_left,real_inner_smul_left,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply,ContinuousLinearMap.zero_apply,fderivInnerCLM_apply,
    inner_zero_left,zero_add,zero_mul,add_zero,smul_eq_mul]
  rw [real_inner_comm ((uProj E) v) ((uProj E) y)]
  ring

theorem gradient_decomposition (u : E) :
    (∑ j ∈ Finset.range (P.J+1), gradient (P.e j) u) = gradient P.r u := by
  have h := HasFDerivAt.sum (fun j (_ : j ∈ Finset.range (P.J+1)) =>
    ((P.e_smooth j).differentiable (by norm_num) u).hasGradientAt.hasFDerivAt)
  have he : (fun v => ∑ j ∈ Finset.range (P.J+1),P.e j v) = P.r := funext P.decomposition
  rw [he] at h
  have hd := h.unique (P.r_smooth.differentiable (by norm_num) u).hasGradientAt.hasFDerivAt
  apply (InnerProductSpace.toDual ℝ E).injective
  simpa only [map_sum] using hd

def response (x : E) : LowerSpace E :=
  pack E ((P.L/P.μ) • x) (P.r ((P.L/P.μ) • x)/P.L) 0

theorem perturbation_at_core (u : E) (_hL : P.L ≠ 0)
    (hcore : ∀ j, j ≤ P.J → |P.r u/P.L| ≤ P.w j/4) :
    P.perturbationU (pack E u (P.r u/P.L) 0) = 0 ∧
      P.perturbationS (pack E u (P.r u/P.L) 0) = -(P.μ/P.L)*P.r u := by
  have hq (j : ℕ) (hj : j ∈ Finset.range (P.J+1)) :
      normal (P.w j) (P.r u/P.L) = P.r u/P.L :=
    normal_core _ _ (P.w_pos j (by have := Finset.mem_range.mp hj; omega))
      (hcore j (by have := Finset.mem_range.mp hj; omega))
  have hdq (j : ℕ) (hj : j ∈ Finset.range (P.J+1)) :
      deriv (normal (P.w j)) (P.r u/P.L) = 1 :=
    normal_deriv_core _ _ (P.w_pos j (by have := Finset.mem_range.mp hj; omega))
      (hcore j (by have := Finset.mem_range.mp hj; omega))
  constructor
  · simp only [perturbationU,uProj_pack,sProj_pack]
    rw [Finset.sum_congr rfl (fun j hj => congrArg (fun a => a • gradient (P.e j) u) (hq j hj)),
      ← Finset.smul_sum,P.gradient_decomposition,smul_smul]
    have he : P.μ/P.L^2*P.r u = P.μ/P.L*(P.r u/P.L) := by
      simp only [div_eq_mul_inv,inv_pow]
      ring
    rw [he,sub_self]
  · simp only [perturbationS,uProj_pack,sProj_pack]
    rw [Finset.sum_congr rfl (fun j hj => by rw [hdq j hj,mul_one]),P.decomposition]

theorem response_stationary (x : E) (hμ : P.μ ≠ 0) (hL : P.L ≠ 0)
    (hcore : ∀ u j, j ≤ P.J → |P.r u/P.L| ≤ P.w j/4) :
    P.lowerY x (P.response x) = 0 := by
  have hc := P.perturbation_at_core ((P.L/P.μ) • x) hL (hcore _)
  simp only [lowerY,response,uProj_pack,sProj_pack,zProj_pack,hc.1,hc.2,add_zero,mul_zero]
  have hu : P.μ • ((P.L/P.μ) • x)-P.L • x = 0 := by
    rw [smul_smul,mul_div_cancel₀ _ hμ,sub_self]
  have hs : P.μ*(P.r ((P.L/P.μ) • x)/P.L)+-(P.μ/P.L)*P.r ((P.L/P.μ) • x) = 0 := by ring
  rw [hu,hs,pack_zero]

theorem response_hasGradient_zero (x : E) (hμ : P.μ ≠ 0) (hL : P.L ≠ 0)
    (hcore : ∀ u j, j ≤ P.J → |P.r u/P.L| ≤ P.w j/4) :
    HasGradientAt (P.lower x) 0 (P.response x) := by
  simpa only [P.response_stationary x hμ hL hcore] using P.lower_hasGradientY x (P.response x)

omit [CompleteSpace E] in
theorem hyperobjective_substitution (x : E) (hL : P.L ≠ 0) :
    P.upper x (P.response x) = P.A ((P.L/P.μ) • x)+P.r ((P.L/P.μ) • x) := by
  simp only [upper,response,uProj_pack,sProj_pack]
  congr 1
  field_simp

end Data
end Bilevel.CompensatedMean
