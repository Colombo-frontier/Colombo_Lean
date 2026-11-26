import MatchingBounds1005.Model
import MatchingBounds1005.RadialComposition

/-! The actual operator-derivative bounds imply exactly the directional
smoothness convention in the manuscript's function class. -/
namespace MatchingBounds1005.Model

open scoped ContDiff NNReal

section Space
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def directionMap (v : E) : ℝ →L[ℝ] E :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight v

@[simp] theorem directionMap_apply (v : E) (t : ℝ) : directionMap v t = t • v := rfl

theorem directionMap_norm_le (v : E) : ‖directionMap v‖ ≤ ‖v‖ := by
  apply (directionMap v).opNorm_le_bound (norm_nonneg v)
  intro t
  rw [directionMap_apply, norm_smul]
  exact le_of_eq (mul_comm _ _)

theorem line_derivative_norm_bound {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (n : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ x : E, ‖iteratedFDeriv ℝ n f x‖ ≤ C) (x v : E) (t : ℝ) :
    |iteratedDeriv n (fun u : ℝ => f (x + u • v)) t| ≤ C * ‖v‖ ^ n := by
  let g : E → ℝ := fun y => f (y + x)
  have hg : ContDiff ℝ ∞ g := hf.comp (contDiff_id.add contDiff_const)
  have he : (fun u : ℝ => f (x + u • v)) = g ∘ directionMap v := by
    funext u
    simp only [g, Function.comp_apply, directionMap_apply, add_comm]
  have hn : (n : WithTop ℕ∞) ≤ ∞ :=
    by exact_mod_cast (show (n : ℕ∞) ≤ ⊤ from le_top)
  rw [he, ← Real.norm_eq_abs, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    (directionMap v).iteratedFDeriv_comp_right hg t hn]
  calc
    _ ≤ ‖iteratedFDeriv ℝ n g (directionMap v t)‖ * ‖directionMap v‖ ^ n := by
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
        (iteratedFDeriv ℝ n g (directionMap v t)).norm_compContinuousLinearMap_le
          (fun _ => directionMap v)
    _ ≤ C * ‖v‖ ^ n := by
      apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg _) (directionMap_norm_le v) n)
        (by positivity) hC
      change ‖iteratedFDeriv ℝ n (fun y => f (y + x)) _‖ ≤ C
      rw [iteratedFDeriv_comp_add_right]
      exact hb _

theorem directional_lipschitz_of_operator_bound {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (q : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ x : E, ‖iteratedFDeriv ℝ (q + 1) f x‖ ≤ C)
    (x v : E) (hv : ‖v‖ = 1) (s t : ℝ) :
    |iteratedDeriv q (fun u : ℝ => f (x + u • v)) t -
      iteratedDeriv q (fun u : ℝ => f (x + u • v)) s| ≤ C * |t - s| := by
  let l : ℝ → ℝ := fun u => f (x + u • v)
  have hl : ContDiff ℝ ∞ l := hf.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have hlevel : ((q + 1 : ℕ) : WithTop ℕ∞) ≤ ∞ :=
    by exact_mod_cast (show (q + 1 : ℕ∞) ≤ ⊤ from le_top)
  have hd : Differentiable ℝ (iteratedDeriv q l) :=
    (contDiff_nat_iff_iteratedDeriv.mp (hl.of_le hlevel)).2 q (Nat.lt_succ_self q)
  let L : ℝ≥0 := ⟨C, hC⟩
  have hbd : ∀ u, ‖deriv (iteratedDeriv q l) u‖₊ ≤ L := by
    intro u
    apply NNReal.coe_le_coe.mp
    change |deriv (iteratedDeriv q l) u| ≤ C
    rw [← iteratedDeriv_succ]
    simpa only [hv, one_pow, mul_one] using line_derivative_norm_bound hf (q + 1) hC hb x v u
  have hLip := lipschitzWith_of_nnnorm_deriv_le hd hbd
  simpa only [Real.dist_eq] using hLip.dist_le_mul t s

end Space

/-- A verified bridge, not an assumption about an unspecified class: these
are exactly the smoothness inequalities required by `InFunctionClass`. -/
theorem inFunctionClass_of_operator_bounds {d p : ℕ} {f : Space d → ℝ}
    (hf : ContDiff ℝ ∞ f) (hgap : ∀ x, f 0 - f x ≤ 1)
    (hb : ∀ q : ℕ, 1 ≤ q → q ≤ p → ∀ x : Space d,
      ‖iteratedFDeriv ℝ (q + 1) f x‖ ≤ 1) : InFunctionClass p f := by
  refine ⟨hf, hgap, ?_⟩
  intro q hq hqp x v hv s t
  simpa only [one_mul] using directional_lipschitz_of_operator_bound hf q
    (by norm_num : (0 : ℝ) ≤ 1) (hb q hq hqp) x v hv s t

end MatchingBounds1005.Model
