import SecondOrder.BoundedLipschitzAlgebra
import SecondOrder.ScalarJetEquality

open scoped BigOperators Classical

namespace SecondOrder
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Global C²,¹ regularity, without a bounded-value requirement. -/
structure ScalarC21 (f : E → ℝ) : Prop where
  smooth : ContDiff ℝ 2 f
  second_lipschitz : ∃ L : ℝ, 0 ≤ L ∧ ∀ x y,
    ‖fderiv ℝ (fderiv ℝ f) x-fderiv ℝ (fderiv ℝ f) y‖ ≤ L*‖x-y‖

/-- Bounded scalar jets through order two, with Lipschitz second derivative.
The first two Lipschitz fields follow from bounds on their derivatives. -/
structure BoundedC21 (f : E → ℝ) : Prop where
  smooth : ContDiff ℝ 2 f
  value : BoundedLipschitz f
  first : BoundedLipschitz (fderiv ℝ f)
  second : BoundedLipschitz (fderiv ℝ (fderiv ℝ f))

theorem BoundedC21.toScalarC21 {f : E → ℝ} (hf : BoundedC21 f) : ScalarC21 f := by
  obtain ⟨L,hL,_,hl⟩ := hf.second
  exact ⟨hf.smooth,L,hL,hl⟩

theorem scalar_second_add {f g : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) :
    fderiv ℝ (fderiv ℝ (fun x => f x+g x)) =
      fun x => fderiv ℝ (fderiv ℝ f) x+fderiv ℝ (fderiv ℝ g) x := by
  have he : fderiv ℝ (fun x => f x+g x) = fun x => fderiv ℝ f x+fderiv ℝ g x :=
    funext (fun x => fderiv_add (hf.differentiable (by norm_num) x) (hg.differentiable (by norm_num) x))
  rw [he]
  exact funext (fun x => fderiv_add
    ((hf.fderiv_right (show (1:WithTop ℕ∞)+1 ≤ 2 by norm_num)).differentiable (by norm_num) x)
    ((hg.fderiv_right (show (1:WithTop ℕ∞)+1 ≤ 2 by norm_num)).differentiable (by norm_num) x))

theorem ScalarC21.add {f g : E → ℝ} (hf : ScalarC21 f) (hg : ScalarC21 g) :
    ScalarC21 (fun x => f x+g x) := by
  letI : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
  letI : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
  obtain ⟨C,hC,hfl⟩ := hf.second_lipschitz
  obtain ⟨D,hD,hgl⟩ := hg.second_lipschitz
  refine ⟨hf.smooth.add hg.smooth,C+D,add_nonneg hC hD,?_⟩
  intro x y
  rw [scalar_second_add hf.smooth hg.smooth]
  calc
    _ = ‖(fderiv ℝ (fderiv ℝ f) x-fderiv ℝ (fderiv ℝ f) y)+
        (fderiv ℝ (fderiv ℝ g) x-fderiv ℝ (fderiv ℝ g) y)‖ := by
          congr 1
          ext u v
          simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.sub_apply]
          ring
    _ ≤ _ := norm_add_le _ _
    _ ≤ C*‖x-y‖+D*‖x-y‖ := add_le_add (hfl x y) (hgl x y)
    _ = (C+D)*‖x-y‖ := by ring

theorem boundedC21_const (c : ℝ) : BoundedC21 (fun _ : E => c) := by
  refine ⟨contDiff_const,boundedLipschitz_const c,?_,?_⟩
  · simpa only [fderiv_const] using boundedLipschitz_const (E := E) (0 : E →L[ℝ] ℝ)
  · simpa using boundedLipschitz_const (E := E) (0 : E →L[ℝ] E →L[ℝ] ℝ)

theorem BoundedC21.add {f g : E → ℝ} (hf : BoundedC21 f) (hg : BoundedC21 g) :
    BoundedC21 (fun x => f x+g x) := by
  refine ⟨hf.smooth.add hg.smooth,hf.value.add hg.value,?_,?_⟩
  · have he : fderiv ℝ (fun x => f x+g x) = fun x => fderiv ℝ f x+fderiv ℝ g x :=
      funext (fun x => fderiv_add (hf.smooth.differentiable (by norm_num) x)
        (hg.smooth.differentiable (by norm_num) x))
    rw [he]
    exact hf.first.add hg.first
  · rw [scalar_second_add hf.smooth hg.smooth]
    exact hf.second.add hg.second

theorem BoundedLipschitz.smul {f : E → ℝ} {g : E → F}
    (hf : BoundedLipschitz f) (hg : BoundedLipschitz g) :
    BoundedLipschitz (fun x => f x • g x) :=
  hf.bilinear hg (ContinuousLinearMap.lsmul ℝ ℝ)

theorem scalar_second_mul {f g : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) :
    fderiv ℝ (fderiv ℝ (fun x => f x*g x)) = fun x =>
      f x • fderiv ℝ (fderiv ℝ g) x+(fderiv ℝ f x).smulRight (fderiv ℝ g x)+
      (g x • fderiv ℝ (fderiv ℝ f) x+(fderiv ℝ g x).smulRight (fderiv ℝ f x)) := by
  have hfd := hf.differentiable (by norm_num)
  have hgd := hg.differentiable (by norm_num)
  have hff := (hf.fderiv_right (show (1:WithTop ℕ∞)+1 ≤ 2 by norm_num)).differentiable (by norm_num)
  have hgf := (hg.fderiv_right (show (1:WithTop ℕ∞)+1 ≤ 2 by norm_num)).differentiable (by norm_num)
  have he : fderiv ℝ (fun y => f y*g y) = fun y => f y • fderiv ℝ g y+g y • fderiv ℝ f y :=
    funext (fun y => ((hfd y).hasFDerivAt.mul (hgd y).hasFDerivAt).fderiv)
  rw [he]
  exact funext (fun x => (((hfd x).hasFDerivAt.smul (hgf x).hasFDerivAt).add
    ((hgd x).hasFDerivAt.smul (hff x).hasFDerivAt)).fderiv)

theorem BoundedC21.mul {f g : E → ℝ} (hf : BoundedC21 f) (hg : BoundedC21 g) :
    BoundedC21 (fun x => f x*g x) := by
  letI : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
  letI : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
  letI : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
  refine ⟨hf.smooth.mul hg.smooth,hf.value.smul hg.value,?_,?_⟩
  · have he : fderiv ℝ (fun x => f x*g x) = fun x => f x • fderiv ℝ g x+g x • fderiv ℝ f x :=
      funext (fun x => fderiv_mul (hf.smooth.differentiable (by norm_num) x)
        (hg.smooth.differentiable (by norm_num) x))
    rw [he]
    exact (hf.value.smul hg.first).add (hg.value.smul hf.first)
  · rw [scalar_second_mul hf.smooth hg.smooth]
    exact ((hf.value.smul hg.second).add
      (hf.first.bilinear hg.first (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)))).add
      ((hg.value.smul hf.second).add
        (hg.first.bilinear hf.first (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ))))

theorem BoundedC21.const_mul {f : E → ℝ} (hf : BoundedC21 f) (c : ℝ) :
    BoundedC21 (fun x => c*f x) := (boundedC21_const c).mul hf

theorem BoundedC21.sub {f g : E → ℝ} (hf : BoundedC21 f) (hg : BoundedC21 g) :
    BoundedC21 (fun x => f x-g x) := by
  simpa only [neg_one_mul,sub_eq_add_neg] using hf.add (hg.const_mul (-1))

theorem BoundedC21.comp_linear {f : F → ℝ} (hf : BoundedC21 f) (L : E →L[ℝ] F) :
    BoundedC21 (f ∘ L) := by
  letI : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
  letI : NormedSpace ℝ (F →L[ℝ] ℝ) := inferInstance
  letI : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
  letI : NormedAddCommGroup (F →L[ℝ] F →L[ℝ] ℝ) := inferInstance
  letI : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
  letI : NormedSpace ℝ (F →L[ℝ] F →L[ℝ] ℝ) := inferInstance
  let A : (F →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] ℝ := (ContinuousLinearMap.compL ℝ E F ℝ).flip L
  let B : (F →L[ℝ] F →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
    ((ContinuousLinearMap.compL ℝ E F (E →L[ℝ] ℝ)).flip L).comp
      (ContinuousLinearMap.compL ℝ F (F →L[ℝ] ℝ) (E →L[ℝ] ℝ) A)
  have h1 : fderiv ℝ (f ∘ L) = fun x => A (fderiv ℝ f (L x)) := by
    funext x
    simpa only [ContinuousLinearMap.fderiv] using
      fderiv_comp x (hf.smooth.differentiable (by norm_num) _) L.differentiableAt
  have h2 : fderiv ℝ (fderiv ℝ (f ∘ L)) = fun x => B (fderiv ℝ (fderiv ℝ f) (L x)) := by
    funext x
    ext u v
    change secondBilinear (f ∘ L) x u v = secondBilinear f (L x) (L u) (L v)
    exact secondBilinear_comp_linear hf.smooth L x u v
  refine ⟨hf.smooth.comp L.contDiff,hf.value.comp_linear L,?_,?_⟩
  · rw [h1]
    exact (hf.first.comp_linear L).map_linear A
  · rw [h2]
    exact (hf.second.comp_linear L).map_linear B

theorem boundedC21_finset_sum {ι : Type*} (s : Finset ι) (f : ι → E → ℝ)
    (hf : ∀ i ∈ s, BoundedC21 (f i)) : BoundedC21 (fun x => ∑ i ∈ s, f i x) := by
  induction s using Finset.induction_on with
  | empty => simpa using boundedC21_const (E := E) 0
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using
      (hf i (Finset.mem_insert_self _ _)).add (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem boundedC21_finset_prod {ι : Type*} (s : Finset ι) (f : ι → E → ℝ)
    (hf : ∀ i ∈ s, BoundedC21 (f i)) : BoundedC21 (fun x => ∏ i ∈ s, f i x) := by
  induction s using Finset.induction_on with
  | empty => simpa using boundedC21_const (E := E) 1
  | @insert i s hi ih =>
    simpa only [Finset.prod_insert hi] using
      (hf i (Finset.mem_insert_self _ _)).mul (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem boundedC21_of_bounds {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    {C₀ C₁ C₂ L : ℝ} (h₀ : 0 ≤ C₀) (h₁ : 0 ≤ C₁) (h₂ : 0 ≤ C₂) (hL : 0 ≤ L)
    (hb₀ : ∀ x, ‖f x‖ ≤ C₀) (hb₁ : ∀ x, ‖fderiv ℝ f x‖ ≤ C₁)
    (hb₂ : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C₂)
    (hl : ∀ x y, ‖fderiv ℝ (fderiv ℝ f) x-fderiv ℝ (fderiv ℝ f) y‖ ≤ L*‖x-y‖) :
    BoundedC21 f := by
  refine ⟨hf,boundedLipschitz_of_derivative_bound (hf.differentiable (by norm_num)) h₀ h₁ hb₀ hb₁,
    boundedLipschitz_of_derivative_bound
      ((hf.fderiv_right (show (1:WithTop ℕ∞)+1 ≤ 2 by norm_num)).differentiable (by norm_num))
      h₁ h₂ hb₁ hb₂, C₂+L, add_nonneg h₂ hL,?_,?_⟩
  · intro x
    exact (hb₂ x).trans (le_add_of_nonneg_right hL)
  · intro x y
    exact (hl x y).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left h₂) (norm_nonneg _))

end
end SecondOrder
