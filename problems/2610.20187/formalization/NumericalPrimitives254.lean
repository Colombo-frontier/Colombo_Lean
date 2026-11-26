import Projection254
import MasterWeights254
import Mathlib.Algebra.BigOperators.Field

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Paper254

/-- The mean perturbation estimate used by the rational projection oracle. -/
theorem metricProject_approximate_potential {d : ℕ} {D : ℝ} (W : Domain d D)
    (Q : Space d ≃L[ℝ] Space d) (a : Space d) (m u : W.carrier) (ξ R : ℝ)
    (hξ : 0 ≤ ξ) (hR : 0 ≤ R)
    (hgap : ‖Q (m.val-a)‖^2 ≤ ‖Q ((metricProject W Q a).val-a)‖^2+ξ)
    (hbound : ‖Q (u.val-(metricProject W Q a).val)‖ ≤ R) :
    ‖Q (u.val-m.val)‖^2-‖Q (u.val-(metricProject W Q a).val)‖^2 ≤
      2*R*Real.sqrt ξ+ξ := by
  let v := Q (u.val-(metricProject W Q a).val)
  let e := Q (m.val-(metricProject W Q a).val)
  have he2 : ‖e‖^2 ≤ ξ := metricProject_objective_gap W Q a m ξ hgap
  have he : ‖e‖ ≤ Real.sqrt ξ := by nlinarith [Real.sq_sqrt hξ,Real.sqrt_nonneg ξ,norm_nonneg e]
  have hid : Q (u.val-m.val) = v-e := by dsimp [v,e]; rw [← map_sub]; congr 1; abel
  rw [hid,norm_sub_sq_real]
  have hi : -⟪v,e⟫ ≤ ‖v‖*‖e‖ := (neg_le_abs _).trans (abs_real_inner_le_norm v e)
  have hm := mul_le_mul hbound he (norm_nonneg e) hR
  change ‖v‖^2-2*⟪v,e⟫+‖e‖^2-‖v‖^2 ≤ _
  nlinarith

/-- Upward probability rounding preserves each positive mass and provides
a uniform lower floor; neither statement assumes a lower bound on v_j. -/
theorem upward_probability_rounding {ι : Type*} [Fintype ι] [Nonempty ι]
    (v : ProbabilityWeights ι) (b : ι → ℝ) (h : ℝ) (hh : 0 < h)
    (hlo : ∀ j, v.weight j+h ≤ b j) (hhi : ∀ j, b j ≤ v.weight j+3*h) :
    let Z := ∑ j,b j
    0 < Z ∧ Z ≤ 1+3*Fintype.card ι*h ∧
      ∀ j, v.weight j/(1+3*Fintype.card ι*h) ≤ b j/Z ∧
        h/(1+3*Fintype.card ι*h) ≤ b j/Z := by
  classical
  let Z := ∑ j,b j
  have hb : ∀ j, 0 < b j := fun j => lt_of_lt_of_le (by linarith [v.nonneg j]) (hlo j)
  have hZ : 0 < Z := Finset.sum_pos (fun j _ => hb j) Finset.univ_nonempty
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) => hhi j)
  have hZup : Z ≤ 1+3*Fintype.card ι*h := by
    simpa only [Finset.sum_add_distrib,v.total,Finset.sum_const,Finset.card_univ,
      nsmul_eq_mul,mul_comm,mul_left_comm,mul_assoc] using hsum
  have hden : 0 < 1+3*Fintype.card ι*h := by positivity
  refine ⟨hZ,hZup,?_⟩
  intro j
  constructor
  · calc
      _ ≤ b j/(1+3*Fintype.card ι*h) := div_le_div_of_nonneg_right (by linarith [hlo j]) hden.le
      _ ≤ b j/Z := div_le_div_of_nonneg_left (hb j).le hZ hZup
  · calc
      _ ≤ b j/(1+3*Fintype.card ι*h) := div_le_div_of_nonneg_right (by linarith [hlo j,v.nonneg j]) hden.le
      _ ≤ b j/Z := div_le_div_of_nonneg_left (hb j).le hZ hZup

theorem upward_rounding_log_overhead (N h : ℝ) (hN : 0 ≤ N) (hh : 0 ≤ h) :
    Real.log (1+3*N*h) ≤ 3*N*h := by
  have hp : 0 < 1+3*N*h := by positivity
  have hl := Real.log_le_sub_one_of_pos hp
  linarith

/-- Smooth positive-part approximation, uniformly in the input. -/
theorem smooth_positive_part_error (x ε : ℝ) (hε : 0 ≤ ε) :
    max x 0 ≤ (x+Real.sqrt (x^2+ε^2))/2 ∧
      (x+Real.sqrt (x^2+ε^2))/2 ≤ max x 0+ε/2 := by
  have hs0 := Real.sqrt_nonneg (x^2+ε^2)
  have hs2 := Real.sq_sqrt (show 0 ≤ x^2+ε^2 by positivity)
  have habs : |x| ≤ Real.sqrt (x^2+ε^2) := by
    nlinarith [sq_abs x,abs_nonneg x]
  have hupper : Real.sqrt (x^2+ε^2) ≤ |x|+ε := by
    nlinarith [sq_abs x,abs_nonneg x,mul_nonneg (abs_nonneg x) hε]
  by_cases hx : 0 ≤ x
  · rw [max_eq_left hx,abs_of_nonneg hx] at *
    constructor <;> linarith
  · have hx' : x ≤ 0 := le_of_not_ge hx
    rw [max_eq_right hx',abs_of_nonpos hx'] at *
    constructor <;> linarith

/-- Exact Newton update contracts the nonnegative square-root error. -/
theorem newton_sqrt_contraction (a x : ℝ) (ha : 0 < a) (hx : Real.sqrt a ≤ x) :
    Real.sqrt a ≤ (x+a/x)/2 ∧
      (x+a/x)/2-Real.sqrt a ≤ (x-Real.sqrt a)/2 := by
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hx0 : 0 < x := hs.trans_le hx
  have hs2 := Real.sq_sqrt ha.le
  have hdiv : a/x ≤ Real.sqrt a := by
    apply (div_le_iff₀ hx0).mpr
    nlinarith [mul_nonneg (show 0 ≤ x-Real.sqrt a by linarith) hs.le]
  constructor
  · have hrel : (a/x)*x=a := div_mul_cancel₀ a hx0.ne'
    have hsq := sq_nonneg (x-Real.sqrt a)
    apply (mul_le_mul_iff_right₀ hx0).mp
    nlinarith
  · linarith

end Paper254
#print axioms Paper254.metricProject_approximate_potential
#print axioms Paper254.upward_probability_rounding
#print axioms Paper254.newton_sqrt_contraction
