import SecondOrder.ScalarJetAlgebra

open scoped BigOperators Classical

namespace SecondOrder
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Equality of the actual value and first two Fréchet derivatives at a point.
Smoothness is retained so the relation can be substituted into products. -/
structure ScalarJetEq (f g : E → ℝ) (x : E) : Prop where
  left_smooth : ContDiff ℝ 2 f
  right_smooth : ContDiff ℝ 2 g
  value : f x = g x
  first : fderiv ℝ f x = fderiv ℝ g x
  second : fderiv ℝ (fderiv ℝ f) x = fderiv ℝ (fderiv ℝ g) x

namespace ScalarJetEq

theorem refl {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x : E) : ScalarJetEq f f x :=
  ⟨hf, hf, rfl, rfl, rfl⟩

theorem symm {f g : E → ℝ} {x : E} (h : ScalarJetEq f g x) : ScalarJetEq g f x :=
  ⟨h.right_smooth, h.left_smooth, h.value.symm, h.first.symm, h.second.symm⟩

theorem trans {f g h : E → ℝ} {x : E} (hfg : ScalarJetEq f g x)
    (hgh : ScalarJetEq g h x) : ScalarJetEq f h x :=
  ⟨hfg.left_smooth, hgh.right_smooth, hfg.value.trans hgh.value,
    hfg.first.trans hgh.first, hfg.second.trans hgh.second⟩

theorem bilinear {f g : E → ℝ} {x : E} (h : ScalarJetEq f g x) (u v : E) :
    secondBilinear f x u v = secondBilinear g x u v := by
  simp only [secondBilinear, h.second]

theorem add {f f' g g' : E → ℝ} {x : E} (hf : ScalarJetEq f f' x)
    (hg : ScalarJetEq g g' x) : ScalarJetEq (fun y => f y+g y) (fun y => f' y+g' y) x := by
  refine ⟨hf.left_smooth.add hg.left_smooth, hf.right_smooth.add hg.right_smooth,
    by rw [hf.value, hg.value], ?_, ?_⟩
  · simp only [fderiv_add (hf.left_smooth.differentiable (by norm_num) x)
      (hg.left_smooth.differentiable (by norm_num) x),
      fderiv_add (hf.right_smooth.differentiable (by norm_num) x)
      (hg.right_smooth.differentiable (by norm_num) x), hf.first, hg.first]
  · have hleft : fderiv ℝ (fun y => f y+g y) = fun y => fderiv ℝ f y+fderiv ℝ g y :=
      funext (fun y => fderiv_add (hf.left_smooth.differentiable (by norm_num) y)
        (hg.left_smooth.differentiable (by norm_num) y))
    have hright : fderiv ℝ (fun y => f' y+g' y) = fun y => fderiv ℝ f' y+fderiv ℝ g' y :=
      funext (fun y => fderiv_add (hf.right_smooth.differentiable (by norm_num) y)
        (hg.right_smooth.differentiable (by norm_num) y))
    rw [hleft, hright, fderiv_add, fderiv_add, hf.second, hg.second]
    all_goals exact (by first
      | exact (hf.left_smooth.fderiv_right (show (1:WithTop ℕ∞)+1 ≤ 2 by norm_num)).differentiable (by norm_num) x
      | exact (hg.left_smooth.fderiv_right (show (1:WithTop ℕ∞)+1 ≤ 2 by norm_num)).differentiable (by norm_num) x
      | exact (hf.right_smooth.fderiv_right (show (1:WithTop ℕ∞)+1 ≤ 2 by norm_num)).differentiable (by norm_num) x
      | exact (hg.right_smooth.fderiv_right (show (1:WithTop ℕ∞)+1 ≤ 2 by norm_num)).differentiable (by norm_num) x)

theorem mul {f f' g g' : E → ℝ} {x : E} (hf : ScalarJetEq f f' x)
    (hg : ScalarJetEq g g' x) : ScalarJetEq (fun y => f y*g y) (fun y => f' y*g' y) x := by
  refine ⟨hf.left_smooth.mul hg.left_smooth, hf.right_smooth.mul hg.right_smooth,
    by rw [hf.value, hg.value], ?_, ?_⟩
  · simp only [fderiv_mul (hf.left_smooth.differentiable (by norm_num) x)
      (hg.left_smooth.differentiable (by norm_num) x),
      fderiv_mul (hf.right_smooth.differentiable (by norm_num) x)
      (hg.right_smooth.differentiable (by norm_num) x), hf.value, hg.value, hf.first, hg.first]
  · ext u v
    change secondBilinear _ x u v = secondBilinear _ x u v
    rw [secondBilinear_mul hf.left_smooth hg.left_smooth,
      secondBilinear_mul hf.right_smooth hg.right_smooth,
      hf.value, hg.value, hf.first, hg.first, hf.bilinear, hg.bilinear]

theorem const_mul {f g : E → ℝ} {x : E} (h : ScalarJetEq f g x) (c : ℝ) :
    ScalarJetEq (fun y => c*f y) (fun y => c*g y) x :=
  (refl (f := fun _ : E => c) contDiff_const x).mul h

theorem sub {f f' g g' : E → ℝ} {x : E} (hf : ScalarJetEq f f' x)
    (hg : ScalarJetEq g g' x) : ScalarJetEq (fun y => f y-g y) (fun y => f' y-g' y) x := by
  simpa only [neg_one_mul, sub_eq_add_neg] using hf.add (hg.const_mul (-1))

theorem sum {ι : Type*} (s : Finset ι) {f g : ι → E → ℝ} {x : E}
    (h : ∀ i ∈ s, ScalarJetEq (f i) (g i) x) :
    ScalarJetEq (fun y => ∑ i ∈ s, f i y) (fun y => ∑ i ∈ s, g i y) x := by
  induction s using Finset.induction_on with
  | empty => simpa using refl (f := fun _ : E => (0:ℝ)) contDiff_const x
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using (h i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

theorem prod {ι : Type*} (s : Finset ι) {f g : ι → E → ℝ} {x : E}
    (h : ∀ i ∈ s, ScalarJetEq (f i) (g i) x) :
    ScalarJetEq (fun y => ∏ i ∈ s, f i y) (fun y => ∏ i ∈ s, g i y) x := by
  induction s using Finset.induction_on with
  | empty => simpa using refl (f := fun _ : E => (1:ℝ)) contDiff_const x
  | @insert i s hi ih =>
    simpa only [Finset.prod_insert hi] using (h i (Finset.mem_insert_self _ _)).mul
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

theorem comp_linear {f g : F → ℝ} (L : E →L[ℝ] F) {x : E}
    (h : ScalarJetEq f g (L x)) : ScalarJetEq (f ∘ L) (g ∘ L) x := by
  refine ⟨h.left_smooth.comp L.contDiff, h.right_smooth.comp L.contDiff, h.value, ?_, ?_⟩
  · rw [fderiv_comp x (h.left_smooth.differentiable (by norm_num) _) L.differentiableAt,
      fderiv_comp x (h.right_smooth.differentiable (by norm_num) _) L.differentiableAt, h.first]
  · ext u v
    change secondBilinear _ x u v = secondBilinear _ x u v
    rw [secondBilinear_comp_linear h.left_smooth, secondBilinear_comp_linear h.right_smooth,
      h.bilinear]

end ScalarJetEq

section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem ScalarJetEq.gradient_eq {f g : H → ℝ} {x : H} (h : ScalarJetEq f g x) :
    gradient f x = gradient g x := by simp only [gradient, h.first]

theorem ScalarJetEq.hessian_eq {f g : H → ℝ} {x : H} (h : ScalarJetEq f g x) :
    fderiv ℝ (gradient f) x = fderiv ℝ (gradient g) x := by
  let R := (InnerProductSpace.toDual ℝ H).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hd (q : H → ℝ) (hq : ContDiff ℝ 2 q) :
      fderiv ℝ (gradient q) x = R.comp (fderiv ℝ (fderiv ℝ q) x) :=
    (R.hasFDerivAt.comp x
      (((hq.fderiv_right (show (1:WithTop ℕ∞)+1 ≤ 2 by norm_num)).differentiable
        (by norm_num) x).hasFDerivAt)).fderiv
  rw [hd f h.left_smooth, hd g h.right_smooth, h.second]

theorem scalarJetEq_zero_of_flat {f : H → ℝ} (hf : ContDiff ℝ 2 f) (x : H)
    (hv : f x=0) (hg : gradient f x=0) (hH : fderiv ℝ (gradient f) x=0) :
    ScalarJetEq f (fun _ => 0) x := by
  letI : NormedSpace ℝ (H →L[ℝ] ℝ) := inferInstance
  letI : NormedAddCommGroup (H →L[ℝ] H →L[ℝ] ℝ) := inferInstance
  have h1 : fderiv ℝ f x=0 := by
    apply norm_eq_zero.mp
    rw [← norm_gradient_eq_fderiv, hg, norm_zero]
  have h2 : fderiv ℝ (fderiv ℝ f) x=0 := by
    apply norm_eq_zero.mp
    rw [← norm_hessian_eq_second_fderiv, hH, norm_zero]
  refine ⟨hf, contDiff_const, hv, ?_, ?_⟩
  · simpa only [fderiv_const] using h1
  · simpa using h2

end Hilbert
end
end SecondOrder
