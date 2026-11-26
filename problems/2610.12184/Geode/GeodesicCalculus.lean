import Geode.Geodesic
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! Explicit derivatives of hyperboloid geodesics and their Lorentz pairings. -/
namespace Geode.Lorentz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem hasDerivAt_form {f g : ℝ → Ambient E} {u v : Ambient E} {t : ℝ}
    (hf : HasDerivAt f u t) (hg : HasDerivAt g v t) :
    HasDerivAt (fun s => form E (f s) (g s))
      (form E u (g t) + form E (f t) v) t := by
  have hff : HasDerivAt (fun s => (f s).1) u.1 t :=
    (ContinuousLinearMap.fst ℝ ℝ E).hasFDerivAt.comp_hasDerivAt t hf
  have hfs : HasDerivAt (fun s => (f s).2) u.2 t :=
    (ContinuousLinearMap.snd ℝ ℝ E).hasFDerivAt.comp_hasDerivAt t hf
  have hgf : HasDerivAt (fun s => (g s).1) v.1 t :=
    (ContinuousLinearMap.fst ℝ ℝ E).hasFDerivAt.comp_hasDerivAt t hg
  have hgs : HasDerivAt (fun s => (g s).2) v.2 t :=
    (ContinuousLinearMap.snd ℝ ℝ E).hasFDerivAt.comp_hasDerivAt t hg
  convert ((hff.neg.mul hgf).add (hfs.inner ℝ hgs)) using 1
  simp only [form]
  ring

noncomputable def rayVelocity (x : Point E) (u : Ambient E) (a t : ℝ) : Ambient E :=
  (Real.sinh (a * t) * a) • x.val + (Real.cosh (a * t) * a) • u

theorem hasDerivAt_rayVector (x : Point E) (u : Ambient E) (a t : ℝ) :
    HasDerivAt (fun s => rayVector x u (a * s)) (rayVelocity x u a t) t := by
  have h : HasDerivAt (fun s : ℝ => a * s) a t := by
    simpa using (hasDerivAt_id t).const_mul a
  exact (h.cosh.smul_const x.val).add (h.sinh.smul_const u)

theorem hasDerivAt_rayVelocity (x : Point E) (u : Ambient E) (a t : ℝ) :
    HasDerivAt (rayVelocity x u a) (a ^ 2 • rayVector x u (a * t)) t := by
  have h : HasDerivAt (fun s : ℝ => a * s) a t := by
    simpa using (hasDerivAt_id t).const_mul a
  have hd := ((h.sinh.mul_const a).smul_const x.val).add
    ((h.cosh.mul_const a).smul_const u)
  convert hd using 1
  simp only [rayVector, smul_add, smul_smul]
  congr 1 <;> congr 1 <;> ring

theorem rayVelocity_tangent (x : Point E) (u : Ambient E)
    (hu : form E x.val u = 0) (hn : form E u u = 1) (a t : ℝ) :
    form E (rayVector x u (a * t)) (rayVelocity x u a t) = 0 := by
  have hux : form E u x.val = 0 := by rw [form_comm]; exact hu
  simp only [rayVector, rayVelocity, form_add_left, form_add_right,
    form_smul_left, form_smul_right, x.normalized, hu, hux, hn]
  ring

theorem rayVelocity_norm_sq (x : Point E) (u : Ambient E)
    (hu : form E x.val u = 0) (hn : form E u u = 1) (a t : ℝ) :
    form E (rayVelocity x u a t) (rayVelocity x u a t) = a ^ 2 := by
  have hux : form E u x.val = 0 := by rw [form_comm]; exact hu
  simp only [rayVelocity, form_add_left, form_add_right,
    form_smul_left, form_smul_right, x.normalized, hu, hux, hn]
  nlinarith [mul_nonneg (sq_nonneg a) (sq_nonneg (Real.sinh (a * t))),
    congrArg (fun r : ℝ => a ^ 2 * r) (Real.cosh_sq_sub_sinh_sq (a * t))]

end Geode.Lorentz
