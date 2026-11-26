import Bilevel.RadialCompression
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Topology.Order.IntermediateValue

/-! Deterministic radial/subspace estimates for the no-cascade homotopy.
The new-column force bounds remain explicit construction-specific premises.
In particular these lemmas do not presume prefix locality or exact coupling. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.NearIdentityConfinement
open RadialWrapper

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem projection_norm_le (W : Submodule ℝ E) [CompleteSpace W] (x : E) :
    ‖W.orthogonalProjection x‖ ≤ ‖x‖ := by
  have h := W.orthogonalProjection.le_opNorm x
  exact h.trans ((mul_le_mul_of_nonneg_right W.orthogonalProjection_norm_le
    (norm_nonneg x)).trans_eq (one_mul _))

theorem projected_inner_bound (W : Submodule ℝ E) [CompleteSpace W]
    (v : E) (p : W) : |⟪v,(p:E)⟫| ≤ ‖W.orthogonalProjection v‖ * ‖(p:E)‖ := by
  rw [← W.inner_orthogonalProjection_eq_of_mem_right p v]
  exact abs_real_inner_le_norm _ _

/-- A still-undisclosed column is controlled for every restricted point,
without any bound on its displacement from the query. -/
theorem undisclosed_readout_bound (W : Submodule ℝ E) [CompleteSpace W]
    (R : ℝ) (hR : 0 < R) (v : E) (p : W) {e : ℝ}
    (he : ‖W.orthogonalProjection v‖ ≤ e) :
    |⟪v,compress R (p:E)⟫| ≤ R*e := by
  let b : W := ⟨compress R (p:E), W.smul_mem _ p.property⟩
  have hi := projected_inner_bound W v b
  have hn := compress_norm_le_radius R hR (p:E)
  have hp : 0 ≤ e := (norm_nonneg _).trans he
  calc
    |⟪v,compress R (p:E)⟫| ≤ ‖W.orthogonalProjection v‖ * ‖compress R (p:E)‖ := hi
    _ ≤ e * R := mul_le_mul he hn (norm_nonneg _) hp
    _ = R*e := mul_comm _ _

/-- The public-radial equation gives the source's `5/4` query-norm bound. -/
theorem query_norm_bound (W : Submodule ℝ E) [CompleteSpace W]
    (p u : W) (hidden : E) {t γ H : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1)
    (hγ : |γ| ≤ 1/4) (hH : ‖hidden‖ ≤ H)
    (heq : u=(1+t*γ) • p + t • W.orthogonalProjection hidden) :
    ‖(u:E)‖ ≤ (5/4)*‖(p:E)‖+H := by
  have hγ' := abs_le.mp hγ
  have hcoeff : |1+t*γ| ≤ 5/4 := by
    have hh : |t*γ| ≤ t*(1/4) := by
      rw [abs_mul, abs_of_nonneg ht.1]
      exact mul_le_mul_of_nonneg_left hγ ht.1
    have ha := abs_add_le (1:ℝ) (t*γ)
    norm_num at ha
    nlinarith [ht.2]
  have hhidden : ‖W.orthogonalProjection hidden‖ ≤ H :=
    (projection_norm_le W hidden).trans hH
  change ‖u‖ ≤ (5/4)*‖p‖+H
  rw [heq]
  have hn := norm_add_le ((1+t*γ) • p) (t • W.orthogonalProjection hidden)
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1] at hn
  have h1 := mul_le_mul_of_nonneg_right hcoeff (norm_nonneg p)
  have h2 : t*‖W.orthogonalProjection hidden‖ ≤ H :=
    (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans hhidden
  linarith

/-- The old query belongs to the pre-disclosure space, even when the homotopy
point belongs to a larger space containing the newly revealed column. -/
theorem old_query_component (Wold : Submodule ℝ E) [CompleteSpace Wold]
    (R : ℝ) (hR : 0 < R) (v p : E) (u : Wold) {e H : ℝ}
    (he : ‖Wold.orthogonalProjection v‖ ≤ e)
    (hH : 0 ≤ H) (hu : ‖(u:E)‖ ≤ (5/4)*‖p‖+H) :
    scale R p * |⟪v,(u:E)⟫| ≤ (5/4)*e*(R+H) := by
  have hp : 0 ≤ e := (norm_nonneg _).trans he
  have hi := (projected_inner_bound Wold v u).trans
    (mul_le_mul_of_nonneg_right he (norm_nonneg (u:E)))
  have hs := (scale_pos R p).le
  have hs1 := scale_le_one R p
  have hr : scale R p * ‖p‖ ≤ R := by
    simpa only [compress, norm_smul, Real.norm_eq_abs,
      abs_of_pos (scale_pos R p)] using compress_norm_le_radius R hR p
  calc
    scale R p * |⟪v,(u:E)⟫| ≤ scale R p * (e*‖(u:E)‖) :=
      mul_le_mul_of_nonneg_left hi hs
    _ ≤ scale R p * (e*((5/4)*‖p‖+H)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hu hp) hs
    _ ≤ (5/4)*e*(R+H) := by
      have h1 := mul_le_mul_of_nonneg_left hr (show 0 ≤ (5/4)*e by positivity)
      have h2 := mul_le_mul_of_nonneg_right hs1 (mul_nonneg hp hH)
      nlinarith

/-- Testing the actual projected equation against a newly inserted whole column
has no projection error. `a` is the ambient nonradial frame force. -/
theorem tested_radial_equation (W : Submodule ℝ E) [CompleteSpace W]
    (p u v : W) (a : E) (α γ t : ℝ)
    (heq : p+t • W.orthogonalProjection (α • a+γ • (p:E))=u) :
    (1+t*γ)*⟪(v:E),(p:E)⟫ = ⟪(v:E),(u:E)⟫-t*α*⟪(v:E),a⟫ := by
  have h := congrArg (fun z : W => ⟪v,z⟫) heq
  dsimp only at h
  rw [inner_add_right, real_inner_smul_right,
    W.inner_orthogonalProjection_eq_of_mem_left] at h
  simp only [inner_add_right, real_inner_smul_right, Submodule.coe_inner] at h
  linarith

/-- The source's quantitative first-exit estimate. Its force premise applies
only while all new coordinates remain in their wider flat intervals. -/
theorem new_readout_bound (R : ℝ) (v p u a : E) {t γ h e H : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) 1) (hγ : |γ| ≤ 1/4) (hh : 0 ≤ h)
    (hquery : scale R p * |⟪v,u⟫| ≤ (5/4)*e*(R+H))
    (htarget : e*(R+H) ≤ h/128) (hforce : |⟪v,a⟫| ≤ h/128)
    (heq : (1+t*γ)*⟪v,p⟫ = ⟪v,u⟫-t*scale R p*⟪v,a⟫) :
    |⟪v,compress R p⟫| ≤ 3*h/128 := by
  have hγ' := abs_le.mp hγ
  have hden : 3/4 ≤ 1+t*γ := by
    have htγ : |t*γ| ≤ t*(1/4) := by
      rw [abs_mul, abs_of_nonneg ht.1]
      exact mul_le_mul_of_nonneg_left hγ ht.1
    have htγ' := (abs_le.mp htγ).1
    nlinarith [ht.2]
  have hs := (scale_pos R p).le
  have hs1 := scale_le_one R p
  have hab := congrArg abs heq
  rw [abs_mul, abs_of_pos (by linarith : 0 < 1+t*γ)] at hab
  have hab' : |⟪v,u⟫-t*scale R p*⟪v,a⟫| ≤
      |⟪v,u⟫|+|t*scale R p*⟪v,a⟫| := by
    simpa only [sub_eq_add_neg, abs_neg] using
      abs_add_le ⟪v,u⟫ (-(t*scale R p*⟪v,a⟫))
  rw [abs_mul, abs_mul, abs_of_nonneg ht.1, abs_of_nonneg hs] at hab'
  have hmul := mul_le_mul_of_nonneg_left hab' hs
  have hforce' : scale R p * (t*scale R p*|⟪v,a⟫|) ≤ h/128 := by
    have hc : 0 ≤ scale R p*(t*scale R p) := mul_nonneg hs (mul_nonneg ht.1 hs)
    have hc1 : scale R p*(t*scale R p) ≤ 1 := by
      have hm := mul_le_of_le_one_left hs ht.2
      have hm' := mul_le_mul_of_nonneg_left hm hs
      nlinarith
    have hm := mul_le_mul_of_nonneg_left hforce hc
    have hm' := mul_le_mul_of_nonneg_right hc1 (show 0 ≤ h/128 by positivity)
    nlinarith
  have hnorm : |⟪v,compress R p⟫| = scale R p * |⟪v,p⟫| := by
    rw [compress, real_inner_smul_right, abs_mul, abs_of_nonneg hs]
  rw [hnorm]
  have hlow := mul_le_mul_of_nonneg_right hden
    (mul_nonneg hs (abs_nonneg ⟪v,p⟫))
  have hqt := mul_le_mul_of_nonneg_left htarget (show (0:ℝ) ≤ 5/4 by norm_num)
  nlinarith

/-- A continuous homotopy cannot leave a barrier if every point at or below
the barrier satisfies a strictly better bound. Apply to the maximum normalized
readout of all newly disclosed columns, not to one column in isolation. -/
theorem continuous_barrier {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    {f : X → ℝ} (hf : Continuous f) (x₀ : X) {a b : ℝ} (hab : a < b)
    (hstart : f x₀ ≤ a) (himprove : ∀ x, f x ≤ b → f x ≤ a) :
    ∀ x, f x ≤ a := by
  intro x
  by_contra h
  have hax : a < f x := lt_of_not_ge h
  by_cases hbx : f x ≤ b
  · exact h (himprove x hbx)
  · have hxb : b ≤ f x := (lt_of_not_ge hbx).le
    obtain ⟨y,hy⟩ := intermediate_value_univ x₀ x hf ⟨hstart.trans hab.le,hxb⟩
    have ha := himprove y (by rw [hy])
    rw [hy] at ha
    exact (not_le_of_gt hab) ha

end Bilevel.NearIdentityConfinement
