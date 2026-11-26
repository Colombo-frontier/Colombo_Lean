import FullJet.SnapshotJet

open scoped ContDiff

namespace FullJet

universe u

section VectorRemainder
variable {E F : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem lineTaylor_contDiff (f : E → F) (p : ℕ) (x : E) : ContDiff ℝ ∞ (lineTaylor f p x) := by
  apply ContDiff.sum
  intro j _
  exact ((iteratedFDeriv ℝ j.val f x).contDiff.comp (contDiff_pi.mpr fun _ => contDiff_id)).const_smul _

noncomputable def taylorResidual (f : E → F) (p : ℕ) (x h : E) : F :=
  f (x + h) - lineTaylor f p x h

theorem taylorResidual_fderiv {f : E → F} {k : ℕ}
    (hf : ContDiff ℝ (k + 1) f) (x h : E) :
    fderiv ℝ (taylorResidual f (k + 1) x) h =
      fderiv ℝ f (x + h) - lineTaylor (fderiv ℝ f) k x h := by
  have hd₁ : Differentiable ℝ (fun y => f (x + y)) :=
    (hf.comp (contDiff_const.add contDiff_id)).differentiable (by simp)
  have hd₂ : Differentiable ℝ (lineTaylor f (k + 1) x) :=
    (lineTaylor_contDiff f (k + 1) x).differentiable (by simp)
  unfold taylorResidual
  rw [fderiv_sub (hd₁ h) (hd₂ h), fderiv_comp_add_left, lineTaylor_fderiv hf]

theorem taylorResidual_fderiv_bound {f : E → F} {k : ℕ}
    (hf : ContDiff ℝ (k + 1) f) (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ a b, ‖iteratedFDeriv ℝ (k + 1) f a - iteratedFDeriv ℝ (k + 1) f b‖ ≤ L * ‖a - b‖)
    (x h : E) : ‖fderiv ℝ (taylorResidual f (k + 1) x) h‖ ≤ L * ‖h‖ ^ (k + 1) := by
  rw [taylorResidual_fderiv hf]
  apply lineTaylor_remainder (hf.fderiv_right (m := k) (by simp)) L hL
  intro a b
  rw [iteratedFDeriv_fderiv_sub_norm]
  exact hlip a b

/-- The residual's Lipschitz constant on a bounded region depends only on
the highest derivative bound and the radius, not on lower derivative magnitudes. -/
theorem taylorResidual_increment_bound {f : E → F} {k : ℕ}
    (hf : ContDiff ℝ (k + 1) f) (L R : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ a b, ‖iteratedFDeriv ℝ (k + 1) f a - iteratedFDeriv ℝ (k + 1) f b‖ ≤ L * ‖a - b‖)
    (x a b : E) (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) :
    ‖taylorResidual f (k + 1) x b - taylorResidual f (k + 1) x a‖ ≤
      (L * R ^ (k + 1)) * ‖b - a‖ := by
  have hd : Differentiable ℝ (taylorResidual f (k + 1) x) := by
    exact ((hf.comp (contDiff_const.add contDiff_id)).differentiable (by simp)).sub
      ((lineTaylor_contDiff f (k + 1) x).differentiable (by simp))
  apply (convex_closedBall (0 : E) R).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => hd z) (fun z hz => ?_)
    (by simpa only [Metric.mem_closedBall, dist_zero_right] using ha)
    (by simpa only [Metric.mem_closedBall, dist_zero_right] using hb)
  have hz' : ‖z‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  apply (taylorResidual_fderiv_bound hf L hL hlip x z).trans
  gcongr

end VectorRemainder

section ComponentGradient
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A component gradient minus the gradient of its stored Taylor snapshot. -/
noncomputable def componentGradientResidual (f : E → ℝ) (p : ℕ) (x h : E) : E →L[ℝ] ℝ :=
  fderiv ℝ f (x + h) - fderiv ℝ (packetPolynomial (fullJet p f x)) h

theorem componentGradientResidual_eq {f : E → ℝ} {k : ℕ}
    (hf : ContDiff ℝ (k + 1) f) (x h : E) :
    componentGradientResidual f (k + 1) x h = taylorResidual (fderiv ℝ f) k x h := by
  rw [componentGradientResidual, packetPolynomial_fullJet, lineTaylor_fderiv hf]
  rfl

/-- The two-point control variate has the p-1 power of the snapshot radius,
which is the variance reduction needed for the matching n exponent. -/
theorem componentGradientResidual_increment {f : E → ℝ} {k : ℕ}
    (hf : ContDiff ℝ (k + 2) f) (L R : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ a b, ‖iteratedFDeriv ℝ (k + 2) f a - iteratedFDeriv ℝ (k + 2) f b‖ ≤ L * ‖a - b‖)
    (x a b : E) (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) :
    ‖componentGradientResidual f (k + 2) x b - componentGradientResidual f (k + 2) x a‖ ≤
      (L * R ^ (k + 1)) * ‖b - a‖ := by
  have hff : ContDiff ℝ ((k + 1 : ℕ) + 1) f := hf.of_le
    (by exact_mod_cast (show k + 1 + 1 ≤ k + 2 by omega))
  rw [componentGradientResidual_eq (k := k + 1) hff x b,
    componentGradientResidual_eq (k := k + 1) hff x a]
  have hD : ContDiff ℝ (k + 1) (fderiv ℝ f) := hf.fderiv_right
    (by exact_mod_cast (show k + 1 + 1 ≤ k + 2 by omega))
  apply taylorResidual_increment_bound hD L R hL _ x a b ha hb
  intro y z
  rw [iteratedFDeriv_fderiv_sub_norm]
  exact hlip y z

end ComponentGradient

end FullJet
