import FullJet.LipschitzTaylor

open Set
open scoped BigOperators ContDiff

namespace FullJet

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def lineTaylor (f : E → F) (p : ℕ) (x h : E) : F :=
  ∑ j : Fin (p + 1), (j.val.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ j.val f x (fun _ => h)

theorem iteratedDeriv_affine_line {f : E → F} {p r : ℕ}
    (hf : ContDiff ℝ p f) (hr : r ≤ p) (x h : E) (t : ℝ) :
    iteratedDeriv r (fun s : ℝ => f (x + s • h)) t =
      iteratedFDeriv ℝ r f (x + t • h) (fun _ => h) := by
  let L : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight h
  have hg : ContDiff ℝ p (fun y : E => f (x + y)) := hf.comp (contDiff_const.add contDiff_id)
  have horder : (r : WithTop ℕ∞) ≤ p := by exact_mod_cast hr
  rw [iteratedDeriv_eq_iteratedFDeriv]
  change iteratedFDeriv ℝ r ((fun y : E => f (x + y)) ∘ L) t (fun _ => 1) = _
  rw [L.iteratedFDeriv_comp_right hg t horder]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, L,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, one_smul,
    iteratedFDeriv_comp_add_left]

theorem lineTaylor_eq_scalarTaylor {f : E → F} {p : ℕ}
    (hf : ContDiff ℝ p f) (x h : E) :
    lineTaylor f p x h = taylorWithinEval (fun t : ℝ => f (x + t • h)) p univ 0 1 := by
  rw [taylor_within_apply, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  rw [iteratedDerivWithin_univ, iteratedDeriv_affine_line hf (Nat.le_of_lt_succ j.isLt)]
  simp

theorem line_highest_derivative_oscillation {f : E → F} {p : ℕ}
    (hf : ContDiff ℝ p f) (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ a b, ‖iteratedFDeriv ℝ p f a - iteratedFDeriv ℝ p f b‖ ≤ L * ‖a - b‖)
    (x h : E) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖iteratedDeriv p (fun s : ℝ => f (x + s • h)) t -
      iteratedDeriv p (fun s : ℝ => f (x + s • h)) 0‖ ≤ L * ‖h‖ ^ (p + 1) := by
  rw [iteratedDeriv_affine_line hf le_rfl, iteratedDeriv_affine_line hf le_rfl]
  simp only [zero_smul, add_zero]
  have hb := (iteratedFDeriv ℝ p f (x + t • h) - iteratedFDeriv ℝ p f x).le_opNorm (fun _ => h)
  simp only [ContinuousMultilinearMap.sub_apply, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hb
  apply hb.trans
  have hl := hlip (x + t • h) x
  rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.1] at hl
  calc
    _ ≤ (L * (t * ‖h‖)) * ‖h‖ ^ p := mul_le_mul_of_nonneg_right hl (pow_nonneg (norm_nonneg _) _)
    _ ≤ (L * (1 * ‖h‖)) * ‖h‖ ^ p := by gcongr; exact ht.2
    _ = _ := by rw [pow_succ]; ring

/-- Dimension-free Taylor remainder under a Lipschitz highest derivative.
The constant is deliberately weakened to one, which only changes order-dependent
constants in the upper complexity rate. -/
theorem lineTaylor_remainder {f : E → F} {p : ℕ}
    (hf : ContDiff ℝ p f) (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ a b, ‖iteratedFDeriv ℝ p f a - iteratedFDeriv ℝ p f b‖ ≤ L * ‖a - b‖)
    (x h : E) : ‖f (x + h) - lineTaylor f p x h‖ ≤ L * ‖h‖ ^ (p + 1) := by
  cases p with
  | zero =>
    have hb := (iteratedFDeriv ℝ 0 f (x + h) - iteratedFDeriv ℝ 0 f x).le_opNorm (fun _ => h)
    simp only [ContinuousMultilinearMap.sub_apply, iteratedFDeriv_zero_apply,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_zero, mul_one] at hb
    have hc := hb.trans (hlip (x + h) x)
    simpa [lineTaylor] using hc
  | succ n =>
    rw [lineTaylor_eq_scalarTaylor hf]
    have hpath : ContDiff ℝ (n + 1) (fun t : ℝ => f (x + t • h)) :=
      hf.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
    have hb := taylor_unit_remainder_of_derivative_oscillation hpath (L * ‖h‖ ^ (n + 2))
      (fun t ht => line_highest_derivative_oscillation hf L hL hlip x h t ht)
    simp only [one_smul] at hb
    apply hb.trans
    apply div_le_self (by positivity)
    exact_mod_cast (show 1 ≤ n.factorial from Nat.factorial_pos n)

end FullJet
