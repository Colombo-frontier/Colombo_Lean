import SphereConcentrationLevy

/-!
A lower-half-mass version of spherical concentration. Positive-part centering
creates a genuine median-zero Lipschitz function, so the conclusion follows
from the already proved spherical theorem without a quantile assumption.
-/

open Set MeasureTheory ProbabilityTheory Real Metric
open Task006.HaarRebalancing
open scoped ENNReal NNReal

namespace Task006.SphereConcentration
noncomputable section

/-- Markov's inequality produces an actual half-mass sublevel event. -/
theorem lower_half_of_integral_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ} {M : ℝ}
    (hf : Integrable f μ) (hnonneg : 0 ≤ᵐ[μ] f) (hM : 0 < M)
    (hmean : (∫ ω, f ω ∂μ) ≤ M) :
    (1 / 2 : ℝ) ≤ μ.real {ω | f ω ≤ 2 * M} := by
  have hmarkov := mul_meas_ge_le_integral_of_nonneg hnonneg hf (2 * M)
  have hbad : μ.real {ω | 2 * M ≤ f ω} ≤ (1 / 2 : ℝ) := by
    nlinarith
  have hcover : {ω | f ω ≤ 2 * M} ∪ {ω | 2 * M ≤ f ω} = univ := by
    ext ω
    simp only [mem_union, mem_setOf_eq, mem_univ, iff_true]
    exact le_total _ _
  have hsum := measureReal_union_le (μ := μ) {ω | f ω ≤ 2 * M} {ω | 2 * M ≤ f ω}
  rw [hcover, probReal_univ] at hsum
  linarith

/-- A half-mass sublevel gives the same universal upper concentration tail,
via the actual positive part of a-m. -/
theorem sphere_lower_half_concentration {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {v : Ω → EuclideanSpace ℝ (Fin d)} (hv : UniformSphereLaw v μ)
    (hd : 0 < d) {a : EuclideanSpace ℝ (Fin d) → ℝ} (ha : Measurable a)
    {H : ℝ≥0} (hH : 0 < H) (hlip : LipschitzOnWith H a (sphere (0 : _) 1))
    {m : ℝ} (hhalf : (1 / 2 : ℝ) ≤ μ.real {ω | a (v ω) ≤ m})
    {t : ℝ} (ht : 0 < t) :
    μ.real {ω | m + t ≤ a (v ω)} ≤
      Real.exp 128 * Real.exp (-(d : ℝ) * t ^ 2 / (128 * (H : ℝ) ^ 2)) := by
  let b : EuclideanSpace ℝ (Fin d) → ℝ := fun q => max (a q - m) 0
  have hb : Measurable b := (ha.sub_const _).max measurable_const
  have hshift : LipschitzWith 1 (fun x : ℝ => x - m) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [Real.dist_eq, NNReal.coe_one, one_mul]
    rw [show x - m - (y - m) = x - y by ring]
  have hmax : LipschitzWith 1 (fun x : ℝ => max (x - m) 0) := hshift.max_const 0
  have hblip : LipschitzOnWith H b (sphere (0 : _) 1) := by
    simpa only [one_mul, Function.comp_def, b] using hmax.comp_lipschitzOnWith hlip
  have hbnonneg (q : EuclideanSpace ℝ (Fin d)) : 0 ≤ b q := le_max_right _ _
  have hblo : (1 / 2 : ℝ) ≤ μ.real {ω | b (v ω) ≤ 0} := by
    have hset : {ω | b (v ω) ≤ 0} = {ω | a (v ω) ≤ m} := by
      ext ω
      simp only [b, mem_setOf_eq, max_le_iff, le_refl, and_true, sub_nonpos]
    rwa [hset]
  have hbhi : (1 / 2 : ℝ) ≤ μ.real {ω | 0 ≤ b (v ω)} := by
    have hset : {ω | 0 ≤ b (v ω)} = univ := by
      ext ω
      simp only [mem_setOf_eq, mem_univ, iff_true]
      exact hbnonneg _
    rw [hset, probReal_univ]
    norm_num
  have htail := sphere_lipschitz_median_concentration_pos hv hd hb hH hblip hblo hbhi ht
  have hset : {ω | t ≤ |b (v ω)|} = {ω | m + t ≤ a (v ω)} := by
    ext ω
    change t ≤ |b (v ω)| ↔ m + t ≤ a (v ω)
    rw [abs_of_nonneg (hbnonneg _)]
    change t ≤ max (a (v ω) - m) 0 ↔ m + t ≤ a (v ω)
    rw [le_max_iff]
    constructor
    · intro h
      rcases h with h | h
      · linarith
      · exact (not_le_of_gt ht h).elim
    · intro h
      left
      linarith
  rwa [hset] at htail

end
end Task006.SphereConcentration
