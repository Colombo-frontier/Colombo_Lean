import HardCurvature254
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

noncomputable section
open Set
namespace Paper254

/-- Scalar Hessian criterion, with derivatives of the actual loss. -/
theorem scalar_expConcave_of_second {S : Set ℝ} (hS : Convex ℝ S)
    (f f' f'' : ℝ → ℝ) (η : ℝ) (hη : 0 ≤ η)
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hcurv : ∀ x ∈ S, η*(f' x)^2 ≤ f'' x) :
    ConcaveOn ℝ S (fun x => Real.exp (-η*f x)) := by
  let g' := fun x => (-η*f' x)*Real.exp (-η*f x)
  let g'' := fun x => (η^2*(f' x)^2-η*f'' x)*Real.exp (-η*f x)
  have hg : ∀ x, HasDerivAt (fun x => Real.exp (-η*f x)) (g' x) x := by
    intro x
    simpa [g',mul_comm] using ((hf x).const_mul (-η)).exp
  have hg' : ∀ x, HasDerivAt g' (g'' x) x := by
    intro x
    convert (((hf' x).const_mul (-η)).mul (hg x)) using 1
    dsimp [g',g'']; ring
  apply concaveOn_of_hasDerivWithinAt2_nonpos hS
    (fun x _ => (hg x).continuousAt.continuousWithinAt)
    (fun x _ => (hg x).hasDerivWithinAt)
    (fun x _ => (hg' x).hasDerivWithinAt)
  intro x hx
  have hc := mul_le_mul_of_nonneg_left (hcurv x (interior_subset hx)) hη
  exact mul_nonpos_of_nonpos_of_nonneg (by nlinarith) (Real.exp_pos _).le

theorem bounded_square_expConcave (y B : ℝ) (hB : 0 < B) :
    ConcaveOn ℝ (Icc (y-B) (y+B))
      (fun z => Real.exp (-(1/B^2)*(1/2*(z-y)^2))) := by
  apply scalar_expConcave_of_second (convex_Icc _ _)
    (fun z => 1/2*(z-y)^2) (fun z => z-y) (fun _ => 1) (1/B^2)
    (by positivity)
  · intro x
    convert (((hasDerivAt_id x).sub_const y).pow 2).const_mul (1/2 : ℝ) using 1 <;> dsimp <;> ring
  · intro x
    simpa using (hasDerivAt_id x).sub_const y
  · intro x hx
    obtain ⟨hxl,hxu⟩ := hx
    have hsq : (x-y)^2 ≤ B^2 := by nlinarith [mul_nonneg (by linarith : 0 ≤ B-(x-y)) (by linarith : 0 ≤ B+(x-y))]
    have hd := (div_le_one (sq_pos_of_pos hB)).mpr hsq
    simpa only [one_div,div_eq_mul_inv,mul_comm,mul_one] using hd

/-- Exp-concavity survives composition with a linear predictor. -/
theorem expConcave_linear_predictor {d : ℕ} (W : Set (Space d)) (hW : Convex ℝ W)
    (L : Space d →L[ℝ] ℝ) (S : Set ℝ) (f : ℝ → ℝ) (η : ℝ)
    (hf : ConcaveOn ℝ S (fun z => Real.exp (-η*f z)))
    (hLS : ∀ w ∈ W, L w ∈ S) : ExpConcaveOn η W (fun w => f (L w)) := by
  refine ⟨hW,?_⟩
  intro x hx y hy a b ha hb hab
  simpa only [map_add,map_smul,smul_eq_mul] using hf.2 (hLS x hx) (hLS y hy) ha hb hab

/-- The portfolio example uses its actual loss; its exponential is affine. -/
theorem portfolio_expConcave {d : ℕ} (W : Set (Space d)) (hW : Convex ℝ W)
    (L : Space d →L[ℝ] ℝ) (hL : ∀ w ∈ W, 0 < L w) :
    ExpConcaveOn 1 W (fun w => -Real.log (L w)) := by
  have he : ∀ w ∈ W, Real.exp (-1 * -Real.log (L w))=L w := by
    intro w hw
    simpa only [neg_mul,one_mul,neg_neg] using Real.exp_log (hL w hw)
  refine ⟨hW,?_⟩
  intro x hx y hy a b ha hb hab
  dsimp only
  rw [he x hx,he y hy,he _ (hW hx hy ha hb hab)]
  simp only [map_add,map_smul,smul_eq_mul,le_refl]

end Paper254
#print axioms Paper254.bounded_square_expConcave
#print axioms Paper254.portfolio_expConcave
