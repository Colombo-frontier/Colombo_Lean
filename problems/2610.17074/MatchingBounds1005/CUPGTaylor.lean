import RandomizedFO2003.OptimizationTaylor
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # Actual cubic Taylor remainders under third-derivative Lipschitzness

All estimates are obtained by integrating actual derivative remainders.
They are stated on the real line, exactly as required by the source class.
-/
noncomputable section
open Set
open scoped ContDiff
open RandomizedFO2003.Calculus

namespace MatchingBounds1005.CUPG

theorem jet_hasDerivAt {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (n : ℕ) (x : ℝ) :
    HasDerivAt (iteratedDeriv n h) (iteratedDeriv (n + 1) h x) x := by
  have hn : ((n + 1 : ℕ) : WithTop ℕ∞) ≤ ∞ :=
    by exact_mod_cast (show (n + 1 : ℕ∞) ≤ ⊤ from le_top)
  have hd := (contDiff_nat_iff_iteratedDeriv.mp (hh.of_le hn)).2 n (Nat.lt_succ_self n)
  simpa only [iteratedDeriv_succ] using (hd x).hasDerivAt

def cubicJet (h : ℝ → ℝ) (x : ℝ) : ℝ :=
  h 0 + deriv h 0 * x + iteratedDeriv 2 h 0 / 2 * x ^ 2 + iteratedDeriv 3 h 0 / 6 * x ^ 3

def firstJet (h : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv h 0 + iteratedDeriv 2 h 0 * x + iteratedDeriv 3 h 0 / 2 * x ^ 2

def secondJet (h : ℝ → ℝ) (x : ℝ) : ℝ :=
  iteratedDeriv 2 h 0 + iteratedDeriv 3 h 0 * x

theorem second_jet_error {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) {L : ℝ}
    (hlip : ∀ x y, |iteratedDeriv 3 h x - iteratedDeriv 3 h y| ≤ L * |x - y|) (x : ℝ) :
    |iteratedDeriv 2 h x - secondJet h x| ≤ L / 2 * |x| ^ 2 := by
  let g : ℝ → ℝ := fun t => iteratedDeriv 2 h (t * x) - secondJet h (t * x)
  let gp : ℝ → ℝ := fun t => x * (iteratedDeriv 3 h (t * x) - iteratedDeriv 3 h 0)
  have hg (t : ℝ) : HasDerivAt g (gp t) t := by
    have hp := (hasDerivAt_id t).mul_const x
    have h1 := (jet_hasDerivAt hh 2 (t * x)).comp t hp
    have h2 := ((hp.const_mul (iteratedDeriv 3 h 0)).const_add (iteratedDeriv 2 h 0))
    convert h1.sub h2 using 1 <;> simp [g, gp, secondJet] <;> ring
  have hb (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) : ‖gp t‖ ≤ (L * |x| ^ 2) * t ^ 1 := by
    have h := mul_le_mul_of_nonneg_left (hlip (t * x) 0) (abs_nonneg x)
    simpa [gp, Real.norm_eq_abs, abs_mul, abs_of_nonneg ht.1, pow_two, mul_assoc, mul_comm,
      mul_left_comm] using h
  have he := norm_at_one_le_of_deriv_power 1 (L * |x| ^ 2) hg (by simp [g, secondJet]) hb
  convert he using 1 <;> simp [g, Real.norm_eq_abs] <;> ring

theorem first_jet_error {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) {L : ℝ}
    (hlip : ∀ x y, |iteratedDeriv 3 h x - iteratedDeriv 3 h y| ≤ L * |x - y|) (x : ℝ) :
    |deriv h x - firstJet h x| ≤ L / 6 * |x| ^ 3 := by
  let g : ℝ → ℝ := fun t => deriv h (t * x) - firstJet h (t * x)
  let gp : ℝ → ℝ := fun t => x * (iteratedDeriv 2 h (t * x) - secondJet h (t * x))
  have hg (t : ℝ) : HasDerivAt g (gp t) t := by
    have hp := (hasDerivAt_id t).mul_const x
    have h1 : HasDerivAt (fun s => deriv h (s * x)) (iteratedDeriv 2 h (t * x) * x) t := by
      simpa only [iteratedDeriv_one, Function.comp_apply, id_eq, one_mul] using
        (jet_hasDerivAt hh 1 (t * x)).comp t hp
    have h2 := (((hp.const_mul (iteratedDeriv 2 h 0)).const_add (deriv h 0)).add
      ((hp.pow 2).const_mul (iteratedDeriv 3 h 0 / 2)))
    convert h1.sub h2 using 1 <;> simp [g, gp, firstJet, secondJet] <;> ring
  have hb (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) : ‖gp t‖ ≤ (L / 2 * |x| ^ 3) * t ^ 2 := by
    have hm := mul_le_mul_of_nonneg_left (second_jet_error hh hlip (t * x)) (abs_nonneg x)
    change |x * (iteratedDeriv 2 h (t * x) - secondJet h (t * x))| ≤ _
    rw [abs_mul]
    convert hm using 1 <;> simp [abs_mul, abs_of_nonneg ht.1] <;> ring
  have he := norm_at_one_le_of_deriv_power 2 (L / 2 * |x| ^ 3) hg (by simp [g, firstJet]) hb
  convert he using 1 <;> simp [g, Real.norm_eq_abs] <;> ring

/-- The exact `L |x|⁴ / 24` cubic Taylor error used in the negative-curvature
and guarded-extrapolation arguments. -/
theorem cubic_jet_error {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) {L : ℝ}
    (hlip : ∀ x y, |iteratedDeriv 3 h x - iteratedDeriv 3 h y| ≤ L * |x - y|) (x : ℝ) :
    |h x - cubicJet h x| ≤ L / 24 * |x| ^ 4 := by
  let g : ℝ → ℝ := fun t => h (t * x) - cubicJet h (t * x)
  let gp : ℝ → ℝ := fun t => x * (deriv h (t * x) - firstJet h (t * x))
  have hg (t : ℝ) : HasDerivAt g (gp t) t := by
    have hp := (hasDerivAt_id t).mul_const x
    have h1 := (hh.differentiable (by norm_num) (t * x)).hasDerivAt.comp t hp
    have h2 := ((((hp.const_mul (deriv h 0)).const_add (h 0)).add
      ((hp.pow 2).const_mul (iteratedDeriv 2 h 0 / 2))).add
        ((hp.pow 3).const_mul (iteratedDeriv 3 h 0 / 6)))
    convert h1.sub h2 using 1 <;> simp [g, gp, cubicJet, firstJet] <;> ring
  have hb (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) : ‖gp t‖ ≤ (L / 6 * |x| ^ 4) * t ^ 3 := by
    have hm := mul_le_mul_of_nonneg_left (first_jet_error hh hlip (t * x)) (abs_nonneg x)
    change |x * (deriv h (t * x) - firstJet h (t * x))| ≤ _
    rw [abs_mul]
    convert hm using 1 <;> simp [abs_mul, abs_of_nonneg ht.1] <;> ring
  have he := norm_at_one_le_of_deriv_power 3 (L / 6 * |x| ^ 4) hg (by simp [g, cubicJet]) hb
  convert he using 1 <;> simp [g, Real.norm_eq_abs] <;> ring

end MatchingBounds1005.CUPG
