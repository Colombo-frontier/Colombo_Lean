import Smoothness2601.SineAdmissible
import Smoothness2601.SineJets

/-! All finite and infinite lower-variable regularity orders for the actual
sine Population, with one common numerical derivative envelope. -/
noncomputable section
open Bilevel.PrimitiveGeometry
open scoped ContDiff
namespace Smoothness2601.SineGeometry
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

omit [CompleteSpace X] in
theorem norm_pack_zero (x : X) : ‖pack x (0:ℝ)‖ = ‖x‖ := by
  rw [norm_pack]
  simp only [norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0),add_zero,Real.sqrt_sq (norm_nonneg x)]

omit [CompleteSpace X] in
theorem norm_zero_pack (y : ℝ) : ‖pack (0:X) y‖ = |y| := by
  rw [norm_pack]
  simp only [norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0),zero_add,Real.norm_eq_abs,Real.sqrt_sq (abs_nonneg y)]

omit [CompleteSpace X] in
theorem lowerGradient_affineWave (B : X → ℝ) (gB : X → X) (m a h : ℝ) (x : X) :
    (fun y => lowerGradient B gB m a h (pack x y)) =
      affineWave h (pack (0:X) m) (pack ((-m*a*h) • gB x) (0:ℝ)) (pack (0:X) (-m*a*B x)) := by
  funext y
  apply (WithLp.equiv 2 (X × ℝ)).injective
  apply Prod.ext
  · change (-m*a*h*Real.sin (y/h)) • gB x = y • (0:X)+(Real.sin (y/h) • ((-m*a*h) • gB x)+Real.cos (y/h) • (0:X))
    simp only [smul_zero,zero_add,add_zero,smul_smul]
    congr 1
    ring
  · change SineLift.lowerGradient m a h (B x) y = y*m+(Real.sin (y/h)*0+Real.cos (y/h)*(-m*a*B x))
    unfold SineLift.lowerGradient
    ring

namespace Profiles
variable (F : Profiles X)

theorem wave_coefficients_bound {m a h : ℝ} (hm : 0 ≤ m) (ha : 0 ≤ a) (hh : 0 ≤ h) (x : X) :
    ‖pack ((-m*a*h) • F.gB x) (0:ℝ)‖+‖pack (0:X) (-m*a*F.B x)‖ ≤ m*a*h*F.C₁+m*a*F.C₀ := by
  rw [norm_pack_zero,norm_zero_pack,norm_smul,Real.norm_eq_abs,
    show |-m*a*h| = m*a*h by rw [abs_mul,abs_mul,abs_neg,abs_of_nonneg hm,abs_of_nonneg ha,abs_of_nonneg hh],
    abs_mul,show |-m*a| = m*a by rw [abs_mul,abs_neg,abs_of_nonneg hm,abs_of_nonneg ha]]
  exact add_le_add (mul_le_mul_of_nonneg_left (F.bound_gB x) (by positivity))
    (mul_le_mul_of_nonneg_left (F.bound_B x) (by positivity))

theorem lower_gradient_contDiff (m a h : ℝ) (x : X) :
    ContDiff ℝ ∞ (fun y => lowerGradient F.B F.gB m a h (pack x y)) := by
  rw [lowerGradient_affineWave]
  exact affineWave_contDiff _ _ _ _

theorem lower_gradient_order_lipschitz {m a h : ℝ} (hm : 0 ≤ m) (ha : 0 ≤ a) (hh : 0 < h)
    {k : ℕ} (hk : 2 ≤ k) (x : X) (y z : ℝ) :
    ‖iteratedFDeriv ℝ k (fun y => lowerGradient F.B F.gB m a h (pack x y)) y-
      iteratedFDeriv ℝ k (fun y => lowerGradient F.B F.gB m a h (pack x y)) z‖ ≤
      (m*a*(F.C₁+F.C₀/h)*h⁻¹^k)*|y-z| := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Nat.add_comm 2 n,lowerGradient_affineWave]
  have hb := affineWave_iteratedFDeriv_lipschitz h (pack (0:X) m)
    (pack ((-m*a*h) • F.gB x) (0:ℝ)) (pack (0:X) (-m*a*F.B x)) n y z
  rw [abs_of_pos (inv_pos.mpr hh)] at hb
  apply hb.trans
  have hc := mul_le_mul_of_nonneg_left (F.wave_coefficients_bound hm ha hh.le x)
    (pow_nonneg (inv_nonneg.mpr hh.le) (n+3))
  have he : h⁻¹^(n+3)*(m*a*h*F.C₁+m*a*F.C₀) = m*a*(F.C₁+F.C₀/h)*h⁻¹^(n+2) := by
    rw [show n+3 = (n+2)+1 by omega,pow_succ]
    field_simp
    ring
  exact (mul_le_mul_of_nonneg_right hc (abs_nonneg _)).trans_eq (by rw [he])

/-- A single coefficient inequality supplies every requested order, including
the infinite cap. Derivatives here are those of the constructed Population. -/
theorem population_higherRegularity {b : Budgets} (S : F.Calibration b)
    (p : WithTop ℕ) (L : ℕ → ℝ) (hL : ∀ j, 0 ≤ L j)
    (henv : ∀ k : ℕ, 2 ≤ k → (k : WithTop ℕ) ≤ p →
      S.m*S.a*(F.C₁+F.C₀/S.h)*S.h⁻¹^k ≤ L (k+1)) :
    (F.population S).HigherRegularity p L := by
  intro q hq hp x
  have hu : (fun y => (F.population S).grad_f (pack x y)) = fun _ : ℝ => pack (F.gA x) S.c := rfl
  have hg : (fun y => (F.population S).grad_g (pack x y)) =
      fun y => lowerGradient F.B F.gB S.m S.a S.h (pack x y) := rfl
  refine ⟨?_,?_,?_,?_⟩
  · rw [hu]
    exact contDiff_const
  · rw [hg]
    exact (F.lower_gradient_contDiff S.m S.a S.h x).of_le
      (by exact_mod_cast (show (q:ℕ∞)+1 ≤ ⊤ from le_top))
  · intro u v
    rw [hu,iteratedFDeriv_const_of_ne (show q ≠ 0 by omega)]
    simp only [Pi.zero_apply,sub_self,norm_zero]
    exact mul_nonneg (hL _) (norm_nonneg _)
  · intro u v
    rw [hg]
    exact (F.lower_gradient_order_lipschitz S.m_nonneg S.a_nonneg S.h_pos (by omega : 2 ≤ q+1) x u v).trans
      (mul_le_mul_of_nonneg_right (henv (q+1) (by omega) hp) (abs_nonneg _))

end Profiles
end Smoothness2601.SineGeometry
