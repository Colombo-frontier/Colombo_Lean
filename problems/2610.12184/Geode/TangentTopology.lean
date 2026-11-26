import Geode.HyperbolicCompact
import Geode.LogMap

/-! Ambient continuity and quantitative comparison of the ambient topology
with the positive Lorentz norm on an actual tangent space. -/
namespace Geode.Lorentz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem continuous_form_ambient :
    Continuous (fun p : Ambient E × Ambient E => form E p.1 p.2) := by
  unfold form
  exact (continuous_fst.fst.neg.mul continuous_snd.fst).add
    (continuous_fst.snd.inner continuous_snd.snd)

theorem continuous_form_left (v : Ambient E) :
    Continuous (fun u : Ambient E => form E u v) :=
  continuous_form_ambient.comp (continuous_id.prodMk continuous_const)

theorem continuous_form_right (u : Ambient E) :
    Continuous (fun v : Ambient E => form E u v) :=
  continuous_form_ambient.comp (continuous_const.prodMk continuous_id)

theorem continuous_form_self : Continuous (fun v : Ambient E => form E v v) :=
  continuous_form_ambient.comp (continuous_id.prodMk continuous_id)

theorem continuous_tangentNorm : Continuous (tangentNorm : Ambient E → ℝ) :=
  Real.continuous_sqrt.comp continuous_form_self

theorem ambient_norm_le_tangent (x : Point E) {v : Ambient E}
    (hv : form E x.val v = 0) : ‖v‖ ≤ x.val.1 * tangentNorm v := by
  have hn := tangent_nonneg x hv
  have hsq : tangentNorm v ^ 2 = form E v v := Real.sq_sqrt hn
  have hnorm : 0 ≤ tangentNorm v := Real.sqrt_nonneg _
  have hsp : ‖v.2‖ ≤ x.val.1 * tangentNorm v := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg x.future.le hnorm)).mp
    rw [mul_pow, hsq]
    exact tangent_spatial_sq_le x hv
  have ht : ‖v.1‖ ≤ ‖v.2‖ := by
    rw [Real.norm_eq_abs]
    apply (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp
    rw [sq_abs]
    rw [form_self] at hn
    linarith only [hn]
  rw [Prod.norm_def]
  exact max_le (ht.trans hsp) hsp

end Geode.Lorentz
