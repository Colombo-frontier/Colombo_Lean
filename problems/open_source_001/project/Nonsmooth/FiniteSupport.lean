import Nonsmooth.SupportCore
import Nonsmooth.MeasurableSimulation

open MeasureTheory
open scoped ENNReal InnerProductSpace
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The literal maximum of the finitely many linear forms in the manuscript. -/
def finiteSupport (a : ι → E) (x : E) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => ⟪a i, x⟫_ℝ)

theorem finiteSupport_attained (a : ι → E) (x : E) : ∃ i, finiteSupport a x = ⟪a i, x⟫_ℝ := by
  obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => ⟪a i, x⟫_ℝ)
  exact ⟨i, he⟩

theorem finiteSupport_ge (a : ι → E) (x : E) (i : ι) : ⟪a i, x⟫_ℝ ≤ finiteSupport a x :=
  Finset.le_sup' (fun i => ⟪a i, x⟫_ℝ) (Finset.mem_univ i)

theorem finiteSupport_convex (a : ι → E) : ConvexOn ℝ Set.univ (finiteSupport a) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy c d hc hd hcd
  apply (Finset.sup'_le_iff _ _).mpr
  intro i hi
  have hcx := mul_le_mul_of_nonneg_left (finiteSupport_ge a x i) hc
  have hdy := mul_le_mul_of_nonneg_left (finiteSupport_ge a y i) hd
  simp only [inner_add_right, inner_smul_right, smul_eq_mul]
  linarith

theorem finiteSupport_homogeneous (a : ι → E) {c : ℝ} (hc : 0 ≤ c) (x : E) :
    finiteSupport a (c • x) = c * finiteSupport a x := by
  apply le_antisymm
  · apply (Finset.sup'_le_iff _ _).mpr
    intro i hi
    simpa only [inner_smul_right] using mul_le_mul_of_nonneg_left (finiteSupport_ge a x i) hc
  · obtain ⟨i, he⟩ := finiteSupport_attained a x
    have h := finiteSupport_ge a (c • x) i
    simpa only [inner_smul_right, he] using h

theorem finiteSupport_lipschitz (a : ι → E) (ha : ∀ i, ‖a i‖ ≤ 2) (x y : E) :
    |finiteSupport a x - finiteSupport a y| ≤ 2 * ‖x - y‖ := by
  have hone (u v : E) : finiteSupport a u - finiteSupport a v ≤ 2 * ‖u - v‖ := by
    obtain ⟨i, hi⟩ := finiteSupport_attained a u
    have hlow := finiteSupport_ge a v i
    have hinner : ⟪a i, u - v⟫_ℝ ≤ 2 * ‖u - v‖ :=
      (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (ha i) (norm_nonneg _))
    rw [inner_sub_right] at hinner
    rw [hi]
    linarith
  apply abs_le.mpr
  have hyx := hone y x
  rw [norm_sub_rev] at hyx
  exact ⟨by linarith, hone x y⟩

theorem finiteSupport_model (a : ι → E) (ha : ∀ i, ‖a i‖ ≤ 2) : SupportModel (finiteSupport a) :=
  ⟨finiteSupport_convex a, fun _ hc x => finiteSupport_homogeneous a hc x,
    fun x _ y _ => finiteSupport_lipschitz a ha x y⟩

theorem finiteSupport_joint_continuous : Continuous (fun p : (ι → E) × E => finiteSupport p.1 p.2) := by
  unfold finiteSupport
  apply Continuous.finset_sup'_apply
  intro i hi
  exact ((continuous_apply i).comp continuous_fst).inner continuous_snd

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

abbrev BoundedSupportRows (E : Type*) [NormedAddCommGroup E] (ι : Type*) := ι → Feasible E 2

def boundedFiniteSupport (a : BoundedSupportRows E ι) (x : E) : ℝ := finiteSupport (fun i => (a i).val) x

theorem boundedFiniteSupport_model (a : BoundedSupportRows E ι) : SupportModel (boundedFiniteSupport a) :=
  finiteSupport_model _ (fun i => (a i).property)

theorem boundedFiniteSupport_measurable (x : E) : Measurable (fun a : BoundedSupportRows E ι => boundedFiniteSupport a x) := by
  have hrows : Measurable (fun a : BoundedSupportRows E ι => fun i => (a i).val) :=
    measurable_pi_lambda _ (fun i => measurable_subtype_coe.comp (measurable_pi_apply i))
  exact finiteSupport_joint_continuous.measurable.comp (hrows.prodMk measurable_const)

/-- The Gaussian truncation radius in the source gives rows of norm at most two after division
by sqrt(d). This map does not assert the Gaussian hardness probabilities. -/
def rescaledSupportRows {d : ℕ} (hd : 0 < d)
    (b : ι → Feasible E (2 * Real.sqrt d)) : BoundedSupportRows E ι := fun i =>
  ⟨(Real.sqrt d)⁻¹ • (b i).val, by
    have hs : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hd)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs)]
    apply (mul_le_mul_iff_of_pos_left hs).mp
    simpa only [← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul, mul_comm (Real.sqrt (d : ℝ)) 2]
      using (b i).property⟩

theorem rescaledSupportRows_measurable {d : ℕ} (hd : 0 < d) :
    Measurable (rescaledSupportRows (E := E) (ι := ι) hd) := by
  apply measurable_pi_lambda
  intro i
  exact (measurable_const.smul (measurable_subtype_coe.comp (measurable_pi_apply i))).subtype_mk

theorem rescaledSupportRows_model {d : ℕ} (hd : 0 < d)
    (b : ι → Feasible E (2 * Real.sqrt d)) : SupportModel (boundedFiniteSupport (rescaledSupportRows hd b)) :=
  boundedFiniteSupport_model _

end
end Nonsmooth
