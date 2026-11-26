import Geode.TangentTopology
import Geode.Subgradient

/-! Joint continuity of the actual logarithm map, including its diagonal,
and closedness of global subgradient support under convergent base points. -/

namespace Geode.Lorentz

open Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem norm_logMap_le (x y : Point E) : ‖logMap x y‖ ≤ x.val.1 * dist x y := by
  simpa only [tangentNorm_logMap] using ambient_norm_le_tangent x (logMap_tangent x y)

theorem continuous_logMap : Continuous (fun p : Point E × Point E => logMap p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have hdist : Continuous (fun q : Point E × Point E => dist q.1 q.2) := continuous_dist
  have hleft : Continuous (fun q : Point E × Point E => q.1.val) :=
    continuous_val.comp continuous_fst
  have hright : Continuous (fun q : Point E × Point E => q.2.val) :=
    continuous_val.comp continuous_snd
  by_cases heq : p.1 = p.2
  · have hlim : Tendsto (fun q : Point E × Point E => q.1.val.1 * dist q.1 q.2)
        (𝓝 p) (𝓝 0) := by
      simpa only [heq, dist_self, mul_zero] using (hleft.fst.mul hdist).tendsto p
    have hz := squeeze_zero_norm (fun q : Point E × Point E => norm_logMap_le q.1 q.2) hlim
    simpa only [ContinuousAt, heq, logMap_self] using hz
  · have hs : Real.sinh (dist p.1 p.2) ≠ 0 :=
      (Real.sinh_pos_iff.mpr (dist_pos.mpr heq)).ne'
    change ContinuousAt (fun q : Point E × Point E =>
      dist q.1 q.2 • ((Real.sinh (dist q.1 q.2))⁻¹ •
        (q.2.val - Real.cosh (dist q.1 q.2) • q.1.val))) p
    exact hdist.continuousAt.smul
      (((Real.continuous_sinh.comp hdist).continuousAt.inv₀ hs).smul
        (hright.sub ((Real.continuous_cosh.comp hdist).smul hleft)).continuousAt)

set_option maxHeartbeats 800000 in
/-- A limit of ordinary global subgradients remains a global subgradient,
even when their base points vary. -/
theorem isSubgradient_of_tendsto {f : Point E → ℝ} (hf : Continuous f)
    {p : ℕ → Point E} {g : ℕ → Ambient E} {x : Point E} {v : Ambient E}
    (hp : Tendsto p atTop (𝓝 x)) (hg : Tendsto g atTop (𝓝 v))
    (hs : ∀ n, IsSubgradient f (p n) (g n)) : IsSubgradient f x v := by
  have hpval : Tendsto (fun n => (p n).val) atTop (𝓝 x.val) :=
    (continuous_val.tendsto x).comp hp
  constructor
  · have hpair : Tendsto (fun n => form E (p n).val (g n)) atTop (𝓝 (form E x.val v)) :=
      (continuous_form_ambient.tendsto (x.val, v)).comp (hpval.prodMk_nhds hg)
    have hzero : Tendsto (fun n => form E (p n).val (g n)) atTop (𝓝 (0 : ℝ)) := by
      convert tendsto_const_nhds using 1
      exact funext (fun n => (hs n).1)
    exact tendsto_nhds_unique hpair hzero
  · intro y
    have hxy : Tendsto (fun n : ℕ => (p n, y)) atTop (𝓝 (x, y)) :=
      hp.prodMk_nhds (tendsto_const_nhds (x := y))
    have hcont : Tendsto (fun q : Point E × Point E => logMap q.1 q.2)
        (𝓝 (x, y)) (𝓝 (logMap x y)) := continuous_logMap.tendsto (x, y)
    have hlog' := hcont.comp hxy
    have hlog : Tendsto (fun n => logMap (p n) y) atTop (𝓝 (logMap x y)) := by
      simpa only [Function.comp_def] using hlog'
    have hpair : Tendsto (fun n => form E (g n) (logMap (p n) y)) atTop
        (𝓝 (form E v (logMap x y))) :=
      (continuous_form_ambient.tendsto (v, logMap x y)).comp (hg.prodMk_nhds hlog)
    exact le_of_tendsto (((hf.tendsto x).comp hp).add hpair)
      (Filter.Eventually.of_forall (fun n => (hs n).2 y))

end Geode.Lorentz
