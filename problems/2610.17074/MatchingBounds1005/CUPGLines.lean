import MatchingBounds1005.Model
import MatchingBounds1005.CUPGEstimate
import MatchingBounds1005.CUPGTaylor

/-! # Directional smoothness at arbitrary line scales

The proofs use exactly the manuscript's directional definition; no tensor
operator-norm conversion is introduced into the upper bound.
-/
noncomputable section
open Set InnerProductSpace
open scoped ContDiff
open RandomizedFO2003.Calculus

namespace MatchingBounds1005.CUPG
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def line (f : E → ℝ) (x v : E) : ℝ → ℝ := fun t => f (x + t • v)

def DirectionalLip (f : E → ℝ) (n : ℕ) (L : ℝ) : Prop :=
  ∀ x v, ‖v‖ = 1 → ∀ s t, |iteratedDeriv n (line f x v) t -
    iteratedDeriv n (line f x v) s| ≤ L * |t - s|

omit [CompleteSpace E] in
theorem line_smooth {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (x v : E) :
    ContDiff ℝ ∞ (line f x v) := hf.comp (contDiff_const.add (contDiff_id.smul contDiff_const))

theorem line_hasDerivAt {f : E → ℝ} (hf : Differentiable ℝ f) (x v : E) (t : ℝ) :
    HasDerivAt (line f x v) ⟪gradient f (x + t • v), v⟫_ℝ t := by
  have hp : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  simpa only [line, Function.comp_def, toDual_apply] using
    (hf _).hasGradientAt.hasFDerivAt.comp_hasDerivAt t hp

theorem directional_lip_scaled {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    {n : ℕ} {L : ℝ} (hdir : DirectionalLip f n L) (x v : E) (s t : ℝ) :
    |iteratedDeriv n (line f x v) t - iteratedDeriv n (line f x v) s| ≤
      L * ‖v‖ ^ (n + 1) * |t - s| := by
  by_cases hv : v = 0
  · subst v
    have he : line f x 0 = fun _ : ℝ => f x := by funext t; simp [line]
    rw [he]
    have hc (k : ℕ) (c : ℝ) : iteratedDeriv k (fun _ : ℝ => c) t =
        iteratedDeriv k (fun _ : ℝ => c) s := by
      induction k generalizing c with
      | zero => rfl
      | succ k ih =>
        rw [iteratedDeriv_succ', show deriv (fun _ : ℝ => c) = fun _ => 0 by funext u; simp]
        exact ih 0
    rw [hc, sub_self, abs_zero]
    simp
  · let u : E := ‖v‖⁻¹ • v
    have hnorm : ‖u‖ = 1 := by
      simp [u, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg v)),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
    have he : line f x v = fun t => line f x u (‖v‖ * t) := by
      funext t
      dsimp [line, u]
      congr 2
      rw [smul_smul]
      congr 1
      field_simp
    have hn : (n : WithTop ℕ∞) ≤ ∞ :=
      by exact_mod_cast (show (n : ℕ∞) ≤ ⊤ from le_top)
    rw [he, iteratedDeriv_comp_const_mul ((line_smooth hf x u).of_le hn), ← mul_sub, abs_mul,
      abs_of_nonneg (pow_nonneg (norm_nonneg v) n)]
    have hh := mul_le_mul_of_nonneg_left (hdir x u hnorm (‖v‖ * s) (‖v‖ * t))
      (pow_nonneg (norm_nonneg v) n)
    convert hh using 1
    rw [← mul_sub, abs_mul, abs_of_nonneg (norm_nonneg v), pow_succ]
    ring

theorem smoothUpper_of_directional {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    {L : ℝ} (hdir : DirectionalLip f 1 L) : SmoothUpper f L := by
  intro x y
  let v := y - x
  let g : ℝ → ℝ := fun t => line f x v t - f x - t * ⟪gradient f x, v⟫_ℝ
  let gp : ℝ → ℝ := fun t => deriv (line f x v) t - deriv (line f x v) 0
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hg (t : ℝ) : HasDerivAt g (gp t) t := by
    have hp := ((line_hasDerivAt hd x v t).sub_const (f x)).sub
      ((hasDerivAt_id t).mul_const ⟪gradient f x, v⟫_ℝ)
    convert hp using 1
    dsimp only [gp]
    rw [(line_hasDerivAt hd x v t).deriv, (line_hasDerivAt hd x v 0).deriv]
    simp
  have hb (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) : ‖gp t‖ ≤ (L * ‖v‖ ^ 2) * t ^ 1 := by
    simpa [gp, Real.norm_eq_abs, abs_of_nonneg ht.1, iteratedDeriv_one] using
      directional_lip_scaled hf hdir x v 0 t
  have hr := norm_at_one_le_of_deriv_power 1 (L * ‖v‖ ^ 2) hg (by simp [g, line]) hb
  have hu := (abs_le.mp (show |g 1| ≤ L * ‖v‖ ^ 2 / 2 by convert hr using 1 <;> norm_num)).2
  dsimp [g, line, v] at hu
  simp only [one_smul, add_sub_cancel, one_mul] at hu
  linarith

theorem model_directional {d p n : ℕ} {f : Model.Space d → ℝ}
    (hf : Model.InFunctionClass p f) (hn : 1 ≤ n) (hnp : n ≤ p) :
    DirectionalLip f n 1 := by
  intro x v hv s t
  simpa only [one_mul, line] using hf.2.2 n hn hnp x v hv s t

end MatchingBounds1005.CUPG
