import BackgroundExamples254

noncomputable section
open Set
namespace Paper254

theorem scalar_expConcave_iff_second {S : Set ℝ} (hS : Convex ℝ S) (ho : IsOpen S)
    (f f' f'' : ℝ → ℝ) (η : ℝ) (hη : 0 < η)
    (hf : ∀ x ∈ S, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ S, HasDerivAt f' (f'' x) x) :
    ConcaveOn ℝ S (fun x => Real.exp (-η*f x)) ↔
      ∀ x ∈ S, η*(f' x)^2 ≤ f'' x := by
  let g' := fun x => (-η*f' x)*Real.exp (-η*f x)
  let g'' := fun x => (η^2*(f' x)^2-η*f'' x)*Real.exp (-η*f x)
  have hg : ∀ x ∈ S, HasDerivAt (fun x => Real.exp (-η*f x)) (g' x) x := by
    intro x hx
    simpa [g',mul_comm] using ((hf x hx).const_mul (-η)).exp
  have hg' : ∀ x ∈ S, HasDerivAt g' (g'' x) x := by
    intro x hx
    convert (((hf' x hx).const_mul (-η)).mul (hg x hx)) using 1
    dsimp [g',g'']; ring
  constructor
  · intro hc x hx
    have ha : AntitoneOn g' S := by
      intro a ha b hb hab
      have hh := hc.antitoneOn_deriv (fun y hy => (hg y hy).differentiableAt) ha hb hab
      rwa [(hg a ha).deriv,(hg b hb).deriv] at hh
    have hn := ha.derivWithin_nonpos (x := x)
    rw [(hg' x hx).hasDerivWithinAt.derivWithin (ho.uniqueDiffWithinAt hx)] at hn
    have hp := Real.exp_pos (-η*f x)
    have hh : η^2*(f' x)^2-η*f'' x ≤ 0 := by
      dsimp [g''] at hn
      nlinarith
    nlinarith
  · intro hc
    apply concaveOn_of_hasDerivWithinAt2_nonpos hS
      (fun x hx => (hg x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hg x (interior_subset hx)).hasDerivWithinAt)
      (fun x hx => (hg' x (interior_subset hx)).hasDerivWithinAt)
    intro x hx
    have hh := mul_le_mul_of_nonneg_left (hc x (interior_subset hx)) hη.le
    exact mul_nonpos_of_nonpos_of_nonneg (by nlinarith) (Real.exp_pos _).le

theorem affine_line_combo {d : ℕ} (x v : Space d) (s t a b : ℝ) (hab : a+b=1) :
    x+(a*s+b*t) • v = a • (x+s • v)+b • (x+t • v) := by
  calc
    x+(a*s+b*t) • v = (a+b) • x+(a*s+b*t) • v := by rw [hab,one_smul]
    _ = _ := by module

/-- The full multidimensional criterion, stated using actual first and second
Fréchet derivatives. The quadratic-form inequality is the Hessian PSD condition. -/
theorem expConcave_iff_hessian {d : ℕ} {S : Set (Space d)}
    (hS : Convex ℝ S) (ho : IsOpen S) (f : Space d → ℝ)
    (F : Space d → Space d →L[ℝ] ℝ)
    (H : Space d → Space d →L[ℝ] Space d →L[ℝ] ℝ)
    (η : ℝ) (hη : 0 < η)
    (hf : ∀ x ∈ S, HasFDerivAt f (F x) x)
    (hF : ∀ x ∈ S, HasFDerivAt F (H x) x) :
    ExpConcaveOn η S f ↔ ∀ x ∈ S, ∀ v, η*(F x v)^2 ≤ H x v v := by
  have hc : ∀ x v : Space d, Convex ℝ {t : ℝ | x+t • v ∈ S} := by
    intro x v s hs t ht a b ha hb hab
    dsimp only [mem_setOf_eq,smul_eq_mul] at *
    rw [affine_line_combo x v s t a b hab]
    exact hS hs ht ha hb hab
  have hopen : ∀ x v : Space d, IsOpen {t : ℝ | x+t • v ∈ S} := by
    intro x v
    exact ho.preimage (continuous_const.add (continuous_id.smul continuous_const))
  have hline : ∀ (x v : Space d) (t : ℝ), HasDerivAt (fun s : ℝ => x+s • v) v t := by
    intro x v t
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have hfirst : ∀ (x v : Space d) t, x+t • v ∈ S →
      HasDerivAt (fun s : ℝ => f (x+s • v)) (F (x+t • v) v) t := by
    intro x v t ht
    exact (hf _ ht).comp_hasDerivAt t (hline x v t)
  have hsecond : ∀ (x v : Space d) t, x+t • v ∈ S →
      HasDerivAt (fun s : ℝ => F (x+s • v) v) (H (x+t • v) v v) t := by
    intro x v t ht
    simpa using ((hF _ ht).clm_apply (hasFDerivAt_const v (x+t • v))).comp_hasDerivAt t (hline x v t)
  have hcriterion := fun x v => scalar_expConcave_iff_second (hc x v) (hopen x v)
    (fun s => f (x+s • v)) (fun s => F (x+s • v) v)
    (fun s => H (x+s • v) v v) η hη (hfirst x v) (hsecond x v)
  constructor
  · intro he x hx v
    have hl : ConcaveOn ℝ {t : ℝ | x+t • v ∈ S}
        (fun t => Real.exp (-η*f (x+t • v))) := by
      refine ⟨hc x v,?_⟩
      intro s hs t ht a b ha hb hab
      simpa only [smul_eq_mul,affine_line_combo x v s t a b hab] using he.2 hs ht ha hb hab
    have hh := (hcriterion x v).mp hl 0 (by simpa using hx)
    simpa using hh
  · intro hh
    refine ⟨hS,?_⟩
    intro x hx y hy a b ha hb hab
    have hl := (hcriterion x (y-x)).mpr (fun t ht => hh _ ht (y-x))
    have h0 : x+(0 : ℝ) • (y-x) ∈ S := by simpa using hx
    have h1 : x+(1 : ℝ) • (y-x) ∈ S := by simpa using hy
    have hl' := hl.2 h0 h1 ha hb hab
    simpa only [smul_eq_mul,affine_line_combo x (y-x) 0 1 a b hab,
      zero_smul,one_smul,add_zero,add_sub_cancel] using hl'

/-- Restriction handles compact and lower-dimensional decision sets whenever
the differentiable loss is defined on an open convex neighborhood. -/
theorem expConcave_of_hessian_neighborhood {d : ℕ} {S U : Set (Space d)}
    (hS : Convex ℝ S) (hSU : S ⊆ U) (hU : Convex ℝ U) (ho : IsOpen U)
    (f : Space d → ℝ) (F : Space d → Space d →L[ℝ] ℝ)
    (H : Space d → Space d →L[ℝ] Space d →L[ℝ] ℝ)
    (η : ℝ) (hη : 0 < η)
    (hf : ∀ x ∈ U, HasFDerivAt f (F x) x)
    (hF : ∀ x ∈ U, HasFDerivAt F (H x) x)
    (hc : ∀ x ∈ U, ∀ v, η*(F x v)^2 ≤ H x v v) : ExpConcaveOn η S f := by
  have hh := (expConcave_iff_hessian hU ho f F H η hη hf hF).mpr hc
  refine ⟨hS,?_⟩
  intro x hx y hy a b ha hb hab
  exact hh.2 (hSU hx) (hSU hy) ha hb hab

/-- A uniform positive Hessian and bounded gradient give the stated
exp-concavity parameter, with no dimension factor. -/
theorem expConcave_of_uniform_hessian {d : ℕ} {S : Set (Space d)}
    (hS : Convex ℝ S) (ho : IsOpen S) (f : Space d → ℝ)
    (F : Space d → Space d →L[ℝ] ℝ)
    (H : Space d → Space d →L[ℝ] Space d →L[ℝ] ℝ)
    (σ G : ℝ) (hσ : 0 < σ) (hG : 0 < G)
    (hf : ∀ x ∈ S, HasFDerivAt f (F x) x)
    (hF : ∀ x ∈ S, HasFDerivAt F (H x) x)
    (hbound : ∀ x ∈ S, ‖F x‖ ≤ G)
    (hcurv : ∀ x ∈ S, ∀ v, σ*‖v‖^2 ≤ H x v v) :
    ExpConcaveOn (σ/G^2) S f := by
  apply (expConcave_iff_hessian hS ho f F H (σ/G^2) (by positivity) hf hF).mpr
  intro x hx v
  have hb : |F x v| ≤ G*‖v‖ := by
    exact (F x).le_opNorm v |>.trans (mul_le_mul_of_nonneg_right (hbound x hx) (norm_nonneg v))
  have hs : (F x v)^2 ≤ G^2*‖v‖^2 := by
    nlinarith [sq_abs (F x v),abs_nonneg (F x v),norm_nonneg v,
      mul_nonneg hG.le (norm_nonneg v)]
  have hm := mul_le_mul_of_nonneg_left hs hσ.le
  apply le_trans _ (hcurv x hx v)
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (sq_pos_of_pos hG)).mpr
  nlinarith

end Paper254
#print axioms Paper254.expConcave_iff_hessian
#print axioms Paper254.expConcave_of_uniform_hessian
