import NCConcave16991.WeakConvexity
import NCConcave16991.MoreauEnvelope
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic.FieldSimp

/-! # Genuine affine quadratics in a real Hilbert space -/

open Set
open scoped InnerProductSpace

namespace NCConcave16991.BaselineHilbert

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def value (L : ℝ) (v x : E) : ℝ := L / 2 * ‖x‖ ^ 2 + ⟪v, x⟫_ℝ

theorem hasGradientAt_value (L : ℝ) (v x : E) :
    HasGradientAt (value L v) (L • x + v) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hn := ((hasFDerivAt_id x).norm_sq.const_mul (L / 2))
  have hv := (innerSL ℝ v).hasFDerivAt (x := x)
  have hlin : InnerProductSpace.toDual ℝ E (L • x + v) =
      (L / 2) • ((2 : ℝ) • innerSL ℝ x) + innerSL ℝ v := by
    ext w
    change ⟪L • x + v,w⟫_ℝ = L / 2 * (2 * ⟪x,w⟫_ℝ) + ⟪v,w⟫_ℝ
    rw [inner_add_left, real_inner_smul_left]
    ring
  rw [hlin]
  convert hn.add hv using 1 <;> first
    | rfl
    | simp only [← Nat.cast_smul_eq_nsmul ℝ, Nat.cast_ofNat, id_eq,
        ContinuousLinearMap.comp_id]

theorem gradient_lipschitz {L : ℝ} (hL : 0 ≤ L) (v x y : E) :
    ‖(L • x + v) - (L • y + v)‖ ≤ L * ‖x - y‖ := by
  rw [show (L • x + v) - (L • y + v) = L • (x-y) by module,
    norm_smul, Real.norm_of_nonneg hL]

theorem weaklyConvex {L : ℝ} (hL : 0 ≤ L) (v : E) : WeaklyConvex L (value L v) :=
  weaklyConvex_of_lipschitz_gradient hL (hasGradientAt_value L v)
    (gradient_lipschitz hL v)

theorem complete_square {L : ℝ} (hL : L ≠ 0) (v x : E) :
    value L v x = L / 2 * ‖x + L⁻¹ • v‖ ^ 2 - ‖v‖ ^ 2 / (2 * L) := by
  simp only [value, norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_smul_right]
  rw [real_inner_comm x v]
  field_simp [hL]
  <;> ring

theorem minimum {L : ℝ} (hL : 0 < L) (v x : E) :
    -(‖v‖ ^ 2 / (2 * L)) ≤ value L v x := by
  rw [complete_square hL.ne']
  nlinarith [sq_nonneg ‖x + L⁻¹ • v‖]

def minimizer (L : ℝ) (v : E) : E := -L⁻¹ • v

theorem value_minimizer {L : ℝ} (hL : L ≠ 0) (v : E) :
    value L v (minimizer L v) = -(‖v‖ ^ 2 / (2 * L)) := by
  rw [complete_square hL]
  simp [minimizer]

theorem bounded_below {L : ℝ} (hL : 0 < L) (v : E) :
    BddBelow (range (value L v)) := by
  refine ⟨-(‖v‖ ^ 2 / (2 * L)), ?_⟩
  rintro _ ⟨x, rfl⟩
  exact minimum hL v x

theorem infimum {L : ℝ} (hL : 0 < L) (v : E) :
    sInf (range (value L v)) = -(‖v‖ ^ 2 / (2 * L)) := by
  apply le_antisymm
  · simpa only [value_minimizer hL.ne'] using
      csInf_le (bounded_below hL v) (mem_range_self (minimizer L v))
  · apply le_csInf (range_nonempty _)
    rintro _ ⟨x, rfl⟩
    exact minimum hL v x

theorem initial_gap {L : ℝ} (hL : 0 < L) (v : E) :
    value L v 0 - sInf (range (value L v)) = ‖v‖ ^ 2 / (2 * L) := by
  rw [infimum hL]
  simp [value]

def prox (L : ℝ) (v c : E) : E := minimizer (3*L) (v - (2*L) • c)

theorem prox_objective_eq (L : ℝ) (v c x : E) :
    proxObjective (value L v) L c x =
      value (3*L) (v - (2*L) • c) x + L * ‖c‖ ^ 2 := by
  simp only [proxObjective, value, norm_sub_sq_real, inner_sub_left,
    real_inner_smul_left]
  rw [real_inner_comm c x]
  ring

theorem isProxPoint {L : ℝ} (hL : 0 < L) (v c : E) :
    IsProxPoint (value L v) L c (prox L v c) := by
  intro x
  rw [prox_objective_eq, prox_objective_eq]
  change value (3*L) (v - (2*L) • c) (minimizer (3*L) (v-(2*L)•c)) + _ ≤ _
  rw [value_minimizer (by positivity : 3*L ≠ 0)]
  exact add_le_add (minimum (by positivity : 0 < 3*L) _ x) (le_refl _)

theorem envelope_hasGradientAt {L : ℝ} (hL : 0 < L) (v c : E) :
    HasGradientAt (moreauEnvelope (value L v) L) ((2/3:ℝ) • (L • c + v)) c := by
  have hg := moreauEnvelope_hasGradientAt hL (weaklyConvex hL.le v) (isProxPoint hL v) c
  convert hg using 1
  simp only [proxResidual, prox, minimizer]
  match_scalars <;> field_simp [hL.ne'] <;> ring

theorem opposite_stationary_disjoint {L ε g : ℝ} (hL : 0 < L)
    (e : E) (he : ‖e‖ = 1) (x : E) (hg : (3/2:ℝ)*ε < g)
    (hp : ‖gradient (moreauEnvelope (value L (g • e)) L) x‖ ≤ ε)
    (hm : ‖gradient (moreauEnvelope (value L ((-g) • e)) L) x‖ ≤ ε) : False := by
  rw [(envelope_hasGradientAt hL _ x).gradient] at hp hm
  have hd := norm_sub_le ((2/3:ℝ) • (L • x + g • e))
    ((2/3:ℝ) • (L • x + (-g) • e))
  have hv : (2/3:ℝ) • (L • x + g • e) - (2/3:ℝ) • (L • x + (-g) • e) =
      (4*g/3) • e := by module
  rw [hv, norm_smul, he, mul_one, Real.norm_eq_abs] at hd
  have habs := le_abs_self (4*g/3)
  linarith

end

end NCConcave16991.BaselineHilbert
