import Mathlib.Probability.Distributions.Uniform
import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Real.Sqrt

open scoped BigOperators InnerProductSpace

namespace SecondOrder

/-! Adapted from the local FullJet2201 project's finite-expectation utilities.
Only mathlib is imported; there is no dependency on that project's results. -/

theorem pmf_toReal_sum {α : Type*} [Fintype α] (p : PMF α) : ∑ a, (p a).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun a _ => p.apply_ne_top a)]
  have h : ∑ a, p a = 1 := by simpa only [tsum_fintype] using p.tsum_coe
  rw [h, ENNReal.toReal_one]

theorem uniform_product_mass {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (a : α) (b : β) :
    ((PMF.uniformOfFintype (α × β)) (a, b)).toReal =
      ((PMF.uniformOfFintype α) a).toReal * ((PMF.uniformOfFintype β) b).toReal := by
  simp [PMF.uniformOfFintype_apply, Fintype.card_prod, ENNReal.mul_inv, ENNReal.toReal_mul]

/-- Bochner expectation on a finite probability space, written as an actual sum. -/
noncomputable def pmfMean {α E : Type*} [Fintype α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (p : PMF α) (X : α → E) : E :=
  ∑ a, (p a).toReal • X a

section Mean
variable {α E F : Type*} [Fintype α]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem pmfMean_congr (p : PMF α) {X Y : α → E} (h : ∀ a, X a = Y a) :
    pmfMean p X = pmfMean p Y := by
  simp only [pmfMean, h]

@[simp] theorem pmfMean_const (p : PMF α) (x : E) : pmfMean p (fun _ => x) = x := by
  simp only [pmfMean, ← Finset.sum_smul, pmf_toReal_sum, one_smul]

theorem pmfMean_add (p : PMF α) (X Y : α → E) :
    pmfMean p (fun a => X a + Y a) = pmfMean p X + pmfMean p Y := by
  simp only [pmfMean, smul_add, Finset.sum_add_distrib]

theorem pmfMean_sub (p : PMF α) (X Y : α → E) :
    pmfMean p (fun a => X a - Y a) = pmfMean p X - pmfMean p Y := by
  simp only [pmfMean, smul_sub, Finset.sum_sub_distrib]

theorem pmfMean_finset_sum {ι : Type*} (p : PMF α) (s : Finset ι) (X : ι → α → E) :
    pmfMean p (fun a => ∑ i ∈ s, X i a) = ∑ i ∈ s, pmfMean p (X i) := by
  simp only [pmfMean, Finset.smul_sum]
  exact Finset.sum_comm

theorem pmfMean_smul (p : PMF α) (c : ℝ) (X : α → E) :
    pmfMean p (fun a => c • X a) = c • pmfMean p X := by
  simp only [pmfMean, Finset.smul_sum]
  exact Finset.sum_congr rfl (fun a _ => smul_comm _ _ _)

theorem pmfMean_linearMap (p : PMF α) (T : E →ₗ[ℝ] F) (X : α → E) :
    pmfMean p (fun a => T (X a)) = T (pmfMean p X) := by
  simp only [pmfMean, map_sum, map_smul]

theorem pmfMean_real (p : PMF α) (X : α → ℝ) :
    pmfMean p X = ∑ a, (p a).toReal * X a := rfl

theorem pmfMean_mul (p : PMF α) (c : ℝ) (X : α → ℝ) :
    pmfMean p (fun a => c * X a) = c * pmfMean p X :=
  pmfMean_smul p c X

theorem pmfMean_mono (p : PMF α) {X Y : α → ℝ} (h : ∀ a, X a ≤ Y a) :
    pmfMean p X ≤ pmfMean p Y := by
  exact Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (h a) ENNReal.toReal_nonneg)

theorem pmfMean_nonneg (p : PMF α) {X : α → ℝ} (h : ∀ a, 0 ≤ X a) :
    0 ≤ pmfMean p X := by
  simpa only [pmfMean_const] using pmfMean_mono p h

theorem pmfMean_le_const (p : PMF α) {X : α → ℝ} (c : ℝ) (h : ∀ a, X a ≤ c) :
    pmfMean p X ≤ c := by
  simpa only [pmfMean_const] using pmfMean_mono p h

theorem norm_pmfMean_le (p : PMF α) (X : α → E) :
    ‖pmfMean p X‖ ≤ pmfMean p (fun a => ‖X a‖) := by
  calc
    _ ≤ ∑ a, ‖(p a).toReal • X a‖ := norm_sum_le _ _
    _ = _ := by simp [pmfMean, norm_smul, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]

@[simp] theorem pmfMean_center (p : PMF α) (X : α → E) :
    pmfMean p (fun a => X a - pmfMean p X) = 0 := by
  rw [pmfMean_sub, pmfMean_const, sub_self]

end Mean

section Inner
variable {α E : Type*} [Fintype α] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem pmfMean_inner_left (p : PMF α) (x : E) (X : α → E) :
    pmfMean p (fun a => ⟪x, X a⟫_ℝ) = ⟪x, pmfMean p X⟫_ℝ := by
  simp [pmfMean, inner_sum, inner_smul_right]

theorem pmfMean_inner_right (p : PMF α) (X : α → E) (x : E) :
    pmfMean p (fun a => ⟪X a, x⟫_ℝ) = ⟪pmfMean p X, x⟫_ℝ := by
  simp [pmfMean, sum_inner, inner_smul_left]

theorem pmfMean_norm_add_sq (p : PMF α) (x : E) (X : α → E) :
    pmfMean p (fun a => ‖x + X a‖ ^ 2) =
      ‖x‖ ^ 2 + 2 * ⟪x, pmfMean p X⟫_ℝ + pmfMean p (fun a => ‖X a‖ ^ 2) := by
  simp only [norm_add_sq_real, pmfMean_add, pmfMean_const, pmfMean_mul, pmfMean_inner_left]

/-- The finite variance identity; no independence hypothesis is needed. -/
theorem pmfMean_variance (p : PMF α) (X : α → E) :
    pmfMean p (fun a => ‖X a - pmfMean p X‖ ^ 2) =
      pmfMean p (fun a => ‖X a‖ ^ 2) - ‖pmfMean p X‖ ^ 2 := by
  simp only [norm_sub_sq_real, pmfMean_sub, pmfMean_add, pmfMean_const,
    pmfMean_mul, pmfMean_inner_right, real_inner_self_eq_norm_sq]
  ring

theorem pmfMean_variance_le (p : PMF α) (X : α → E) :
    pmfMean p (fun a => ‖X a - pmfMean p X‖ ^ 2) ≤ pmfMean p (fun a => ‖X a‖ ^ 2) := by
  rw [pmfMean_variance]
  exact sub_le_self _ (sq_nonneg _)

theorem sq_norm_pmfMean_le (p : PMF α) (X : α → E) :
    ‖pmfMean p X‖ ^ 2 ≤ pmfMean p (fun a => ‖X a‖ ^ 2) := by
  have h := pmfMean_nonneg p (fun a => sq_nonneg ‖X a - pmfMean p X‖)
  rw [pmfMean_variance] at h
  linarith

theorem pmfMean_norm_le_sqrt (p : PMF α) (X : α → E) :
    pmfMean p (fun a => ‖X a‖) ≤ Real.sqrt (pmfMean p (fun a => ‖X a‖ ^ 2)) := by
  apply Real.le_sqrt_of_sq_le
  have h := sq_norm_pmfMean_le p (fun a => ‖X a‖)
  simpa only [Real.norm_eq_abs, sq_abs, abs_norm] using h

end Inner

section Uniform
variable {α β E : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def uniformMean (X : α → E) : E := pmfMean (PMF.uniformOfFintype α) X

theorem uniformMean_congr {X Y : α → E} (h : ∀ a, X a = Y a) :
    uniformMean X = uniformMean Y := pmfMean_congr _ h

@[simp] theorem uniformMean_const (x : E) : uniformMean (fun _ : α => x) = x :=
  pmfMean_const _ _

theorem uniformMean_add (X Y : α → E) :
    uniformMean (fun a => X a + Y a) = uniformMean X + uniformMean Y := pmfMean_add _ _ _

theorem uniformMean_sub (X Y : α → E) :
    uniformMean (fun a => X a - Y a) = uniformMean X - uniformMean Y := pmfMean_sub _ _ _

theorem uniformMean_smul (c : ℝ) (X : α → E) :
    uniformMean (fun a => c • X a) = c • uniformMean X := pmfMean_smul _ _ _

theorem uniformMean_mul (c : ℝ) (X : α → ℝ) :
    uniformMean (fun a => c * X a) = c * uniformMean X := pmfMean_mul _ _ _

theorem uniformMean_mono {X Y : α → ℝ} (h : ∀ a, X a ≤ Y a) :
    uniformMean X ≤ uniformMean Y := pmfMean_mono _ h

theorem uniformMean_nonneg {X : α → ℝ} (h : ∀ a, 0 ≤ X a) :
    0 ≤ uniformMean X := pmfMean_nonneg _ h

theorem uniformMean_le_const {X : α → ℝ} (c : ℝ) (h : ∀ a, X a ≤ c) :
    uniformMean X ≤ c := pmfMean_le_const _ _ h

theorem uniformMean_eq (X : α → E) :
    uniformMean X = (Fintype.card α : ℝ)⁻¹ • ∑ a, X a := by
  simp [uniformMean, pmfMean, PMF.uniformOfFintype_apply, ENNReal.toReal_inv, Finset.smul_sum]

theorem uniformMean_equiv (e : α ≃ β) (X : β → E) :
    uniformMean (fun a => X (e a)) = uniformMean X := by
  rw [uniformMean_eq, uniformMean_eq, Fintype.card_congr e, Equiv.sum_comp e]

theorem uniformMean_prod (X : α × β → E) :
    uniformMean X = uniformMean (fun a => uniformMean (fun b => X (a, b))) := by
  simp only [uniformMean, pmfMean, Fintype.sum_prod_type, uniform_product_mass,
    mul_smul, Finset.smul_sum]

/-- Separate a uniform finite sequence into its past and its independent last sample. -/
theorem uniformMean_snoc (t : ℕ) (X : (Fin (t + 1) → α) → E) :
    uniformMean X = uniformMean (fun past : Fin t → α =>
      uniformMean (fun a => X (Fin.snoc past a))) := by
  let e : ((Fin t → α) × α) ≃ (Fin (t + 1) → α) :=
    (Equiv.prodComm _ _).trans (Fin.snocEquiv (fun _ => α))
  rw [← uniformMean_equiv e X, uniformMean_prod]
  rfl

end Uniform

end SecondOrder

