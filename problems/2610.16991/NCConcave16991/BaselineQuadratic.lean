import NCConcave16991.MoreauEnvelope
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp

/-!
# An actual hidden affine quadratic family

Every component has exactly the same quadratic curvature.  The hidden component
only changes an affine term.  The statements below concern the actual infimum
and actual Moreau envelope, including their derivatives; no stationarity oracle
or envelope-gradient formula is postulated.
-/

open Set
open scoped BigOperators

namespace NCConcave16991.BaselineQuadratic

noncomputable section

def value (L a x : ℝ) : ℝ := L * x ^ 2 / 2 + a * x

theorem hasDerivAt_value (L a x : ℝ) :
    HasDerivAt (value L a) (L * x + a) x := by
  convert (((hasDerivAt_id x).pow 2).const_mul L |>.div_const 2).add
    ((hasDerivAt_id x).const_mul a) using 1
  · funext t; dsimp [value] <;> ring
  · dsimp; ring

theorem hasGradientAt_value (L a x : ℝ) :
    HasGradientAt (value L a) (L * x + a) x := by
  simpa using (hasDerivAt_value L a x).hasGradientAt

theorem gradient_value (L a x : ℝ) : gradient (value L a) x = L * x + a :=
  (hasGradientAt_value L a x).gradient

theorem gradient_lipschitz {L : ℝ} (hL : 0 ≤ L) (a x y : ℝ) :
    ‖gradient (value L a) x - gradient (value L a) y‖ ≤ L * ‖x - y‖ := by
  rw [gradient_value, gradient_value, show L * x + a - (L * y + a) = L * (x-y) by ring,
    norm_mul, Real.norm_of_nonneg hL]

theorem complete_square {L : ℝ} (hL : L ≠ 0) (a x : ℝ) :
    value L a x = L / 2 * (x + a / L) ^ 2 - a ^ 2 / (2 * L) := by
  unfold value
  field_simp
  <;> ring

theorem minimum {L : ℝ} (hL : 0 < L) (a x : ℝ) :
    -(a ^ 2 / (2 * L)) ≤ value L a x := by
  rw [complete_square hL.ne']
  nlinarith [sq_nonneg (x + a / L)]

theorem value_minimizer {L : ℝ} (hL : L ≠ 0) (a : ℝ) :
    value L a (-a / L) = -(a ^ 2 / (2 * L)) := by
  rw [complete_square hL]
  ring

theorem bounded_below {L : ℝ} (hL : 0 < L) (a : ℝ) :
    BddBelow (range (value L a)) := by
  refine ⟨-(a ^ 2 / (2*L)), ?_⟩
  rintro _ ⟨x, rfl⟩
  exact minimum hL a x

theorem infimum {L : ℝ} (hL : 0 < L) (a : ℝ) :
    sInf (range (value L a)) = -(a ^ 2 / (2 * L)) := by
  apply le_antisymm
  · simpa only [value_minimizer hL.ne'] using
      csInf_le (bounded_below hL a) (mem_range_self (-a/L))
  · apply le_csInf (range_nonempty _)
    rintro _ ⟨x, rfl⟩
    exact minimum hL a x

theorem initial_gap {L : ℝ} (hL : 0 < L) (a : ℝ) :
    value L a 0 - sInf (range (value L a)) = a ^ 2 / (2 * L) := by
  rw [infimum hL]
  simp [value]

def prox (L a c : ℝ) : ℝ := (2 * L * c - a) / (3 * L)

def envelopeFormula (L a c : ℝ) : ℝ :=
  L / 3 * c ^ 2 + 2 * a / 3 * c - a ^ 2 / (6 * L)

theorem prox_complete_square {L : ℝ} (hL : L ≠ 0) (a c x : ℝ) :
    proxObjective (value L a) L c x =
      envelopeFormula L a c + (3*L/2) * (x - prox L a c)^2 := by
  simp only [proxObjective, Real.norm_eq_abs, sq_abs, value, prox, envelopeFormula]
  field_simp
  <;> ring

theorem isProxPoint {L : ℝ} (hL : 0 < L) (a c : ℝ) :
    IsProxPoint (value L a) L c (prox L a c) := by
  intro x
  rw [prox_complete_square hL.ne', prox_complete_square hL.ne']
  simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    add_zero]
  have := sq_nonneg (x - prox L a c)
  nlinarith

theorem envelope_eq {L : ℝ} (hL : 0 < L) (a c : ℝ) :
    moreauEnvelope (value L a) L c = envelopeFormula L a c := by
  rw [moreauEnvelope_eq_minimizedValue (isProxPoint hL a)]
  change proxObjective (value L a) L c (prox L a c) = _
  rw [prox_complete_square hL.ne']
  simp

theorem envelope_hasGradientAt {L : ℝ} (hL : 0 < L) (a c : ℝ) :
    HasGradientAt (moreauEnvelope (value L a) L) ((2/3:ℝ)*(L*c+a)) c := by
  have he : moreauEnvelope (value L a) L = envelopeFormula L a :=
    funext (envelope_eq hL a)
  rw [he]
  have hd : HasDerivAt (envelopeFormula L a) ((2/3:ℝ)*(L*c+a)) c := by
    convert (((((hasDerivAt_id c).pow 2).const_mul (L/3)).add
      ((hasDerivAt_id c).const_mul (2*a/3))).sub_const (a^2/(6*L))) using 1
    · funext t; dsimp [envelopeFormula] <;> ring
    · dsimp; ring
  simpa using hd.hasGradientAt

theorem envelope_gradient {L : ℝ} (hL : 0 < L) (a c : ℝ) :
    gradient (moreauEnvelope (value L a) L) c = (2/3:ℝ)*(L*c+a) :=
  (envelope_hasGradientAt hL a c).gradient

def component {n : ℕ} (L a : ℝ) (j i : Fin n) (x : ℝ) : ℝ :=
  value L (if i = j then (n:ℝ)*a else 0) x

theorem component_hasGradientAt {n : ℕ} (L a : ℝ) (j i : Fin n) (x : ℝ) :
    HasGradientAt (component L a j i)
      (L*x + if i=j then (n:ℝ)*a else 0) x :=
  hasGradientAt_value L _ x

theorem component_individualSmooth {n : ℕ} {L : ℝ} (hL : 0 ≤ L)
    (a : ℝ) (j i : Fin n) (x y : ℝ) :
    ‖gradient (component L a j i) x - gradient (component L a j i) y‖ ≤ L*‖x-y‖ :=
  gradient_lipschitz hL _ x y

theorem component_average {n : ℕ} (hn : 0 < n) (L a : ℝ) (j : Fin n) (x : ℝ) :
    (n:ℝ)⁻¹ * ∑ i, component L a j i x = value L a x := by
  have hn' : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  simp only [component, value, add_mul, Finset.sum_add_distrib]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  <;> ring

theorem component_eq_base {n : ℕ} (L a : ℝ) {j i : Fin n} (h : i ≠ j) :
    component L a j i = value L 0 := by
  funext x
  simp only [component, if_neg h]

/-- The two actual Moreau stationary regions are disjoint. -/
theorem opposite_stationary_disjoint {L ε g x : ℝ} (hL : 0 < L)
    (hg : (3/2:ℝ)*ε < g)
    (hplus : ‖gradient (moreauEnvelope (value L g) L) x‖ ≤ ε)
    (hminus : ‖gradient (moreauEnvelope (value L (-g)) L) x‖ ≤ ε) : False := by
  rw [envelope_gradient hL] at hplus hminus
  have hp := (abs_le.mp hplus).2
  have hm := (abs_le.mp hminus).1
  linarith

end

end NCConcave16991.BaselineQuadratic
