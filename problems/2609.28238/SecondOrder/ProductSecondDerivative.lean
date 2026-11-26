import SecondOrder.DirectionalCurvature

open scoped BigOperators Classical

namespace SecondOrder
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def secondBilinear (f : E → ℝ) (x u v : E) : ℝ := fderiv ℝ (fderiv ℝ f) x u v

theorem secondBilinear_mul {f g : E → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (x u v : E) :
    secondBilinear (fun y => f y*g y) x u v =
      f x*secondBilinear g x u v+g x*secondBilinear f x u v+
      fderiv ℝ f x u*fderiv ℝ g x v+fderiv ℝ g x u*fderiv ℝ f x v := by
  have hfd := hf.differentiable (by norm_num)
  have hgd := hg.differentiable (by norm_num)
  have hff := (hf.fderiv_right (show (1:WithTop ℕ∞)+1 ≤ 2 by norm_num)).differentiable (by norm_num)
  have hgf := (hg.fderiv_right (show (1:WithTop ℕ∞)+1 ≤ 2 by norm_num)).differentiable (by norm_num)
  have he : fderiv ℝ (fun y => f y*g y) = fun y => f y • fderiv ℝ g y+g y • fderiv ℝ f y :=
    funext (fun y => ((hfd y).hasFDerivAt.mul (hgd y).hasFDerivAt).fderiv)
  have hd := (((hfd x).hasFDerivAt.smul (hgf x).hasFDerivAt).add
    ((hgd x).hasFDerivAt.smul (hff x).hasFDerivAt)).fderiv
  rw [secondBilinear, he, hd]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul, secondBilinear]
  ring

/-- Product differentiation with normalized first and second jets. This is an
identity for actual Fréchet derivatives, including vanishing product values. -/
theorem product_normalized_jets {ι : Type*} (s : Finset ι) (f : ι → E → ℝ)
    (hf : ∀ i ∈ s, ContDiff ℝ 2 (f i)) (x u v : E) (a b c : ι → ℝ)
    (ha : ∀ i ∈ s, fderiv ℝ (f i) x u = f i x*a i)
    (hb : ∀ i ∈ s, fderiv ℝ (f i) x v = f i x*b i)
    (hc : ∀ i ∈ s, secondBilinear (f i) x u v = f i x*c i) :
    fderiv ℝ (fun y => ∏ i ∈ s, f i y) x u = (∏ i ∈ s, f i x)*(∑ i ∈ s, a i) ∧
    fderiv ℝ (fun y => ∏ i ∈ s, f i y) x v = (∏ i ∈ s, f i x)*(∑ i ∈ s, b i) ∧
    secondBilinear (fun y => ∏ i ∈ s, f i y) x u v =
      (∏ i ∈ s, f i x)*((∑ i ∈ s, c i)+(∑ i ∈ s, a i)*(∑ i ∈ s, b i)-
        ∑ i ∈ s, a i*b i) := by
  induction s using Finset.induction_on with
  | empty => simp [secondBilinear]
  | @insert i s hi ih =>
    have hfi := hf i (Finset.mem_insert_self _ _)
    have hfs : ∀ j ∈ s, ContDiff ℝ 2 (f j) := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have hp : ContDiff ℝ 2 (fun y => ∏ j ∈ s, f j y) := contDiff_prod (fun j hj => hfs j hj)
    obtain ⟨ihu, ihv, ih2⟩ := ih hfs
      (fun j hj => ha j (Finset.mem_insert_of_mem hj))
      (fun j hj => hb j (Finset.mem_insert_of_mem hj))
      (fun j hj => hc j (Finset.mem_insert_of_mem hj))
    have hd := ((hfi.differentiable (by norm_num) x).hasFDerivAt.mul
      (hp.differentiable (by norm_num) x).hasFDerivAt).fderiv
    simp only [Finset.prod_insert hi, Finset.sum_insert hi]
    rw [secondBilinear_mul hfi hp, hd]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      ha i (Finset.mem_insert_self _ _), hb i (Finset.mem_insert_self _ _),
      hc i (Finset.mem_insert_self _ _), ihu, ihv, ih2]
    constructor
    · ring
    constructor <;> ring

end
end SecondOrder
