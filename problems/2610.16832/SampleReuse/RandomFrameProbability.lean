import SampleReuse.RandomFrameLaw

noncomputable section
namespace SampleReuse.RandomFrame

open MeasureTheory RandomizedFO2003 Rotations
open scoped InnerProductSpace ENNReal

variable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]

theorem product_event_bound (μ : Measure Ω) (ν : Measure Ξ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (s : Set (Ω × Ξ)) (hs : MeasurableSet s) {B : ℝ} (hB : 0 ≤ B)
    (hfiber : ∀ ω, ν.real ((Prod.mk ω) ⁻¹' s) ≤ B) : (μ.prod ν).real s ≤ B := by
  apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hB).mp
  rw [Measure.prod_apply hs]
  calc
    _ ≤ ∫⁻ _ω : Ω, ENNReal.ofReal B ∂μ := by
      apply lintegral_mono
      intro ω
      exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hB).mpr (hfiber ω)
    _ = _ := by simp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
variable {ι κ : Type*}

/-- Internal random coins have their actual independent product law with the
Haar frame. Queries may depend arbitrarily and measurably on those coins and on
the revealed columns. Only queries inside radius `R` enter the event. -/
theorem coin_query_inside_tail [Fintype κ] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (e : ι → E) (he : Orthonormal ℝ e) (a : κ → ι) (ha : Function.Injective a)
    (j : ι) (hj : ∀ k, a k ≠ j) (q : Ω × (κ → E) → E) (hq : Measurable q)
    {R t : ℝ} (hR : 0 < R) (ht : 0 < t) :
    (μ.prod (haarLaw E)).real {p | ‖q (p.1, fun k => isometry E p.2 (e (a k)))‖ ≤ R ∧
      t ≤ |⟪q (p.1, fun k => isometry E p.2 (e (a k))), isometry E p.2 (e j)⟫_ℝ|} ≤
      2 * Real.exp (-((Module.finrank ℝ E - Fintype.card κ : ℕ) : ℝ) * t ^ 2 /
        (2 * R ^ 2)) := by
  apply product_event_bound μ (haarLaw E)
  · have hquery : Measurable (fun p : Ω × Rotation E =>
        q (p.1, fun k => isometry E p.2 (e (a k)))) :=
      hq.comp (measurable_fst.prodMk (measurable_pi_lambda _
        (fun k => (measurable_orbit E (e (a k))).comp measurable_snd)))
    apply (measurableSet_le hquery.norm measurable_const).inter
    have hi : Measurable (fun p : Ω × Rotation E =>
        ⟪q (p.1, fun k => isometry E p.2 (e (a k))), isometry E p.2 (e j)⟫_ℝ) :=
      (show Continuous (fun z : E × E => ⟪z.1, z.2⟫_ℝ) from
        continuous_fst.inner continuous_snd).measurable.comp
          (hquery.prodMk ((measurable_orbit E (e j)).comp measurable_snd))
    exact measurableSet_le (measurable_const (a := t)) hi.abs
  · positivity
  · intro ω
    exact revealed_query_inside_tail e he a ha j hj (fun z => q (ω, z))
      (hq.comp (measurable_const.prodMk measurable_id)) hR ht

/-- A finite family of adaptive query/hidden-column tests, including a terminal
output, obeys a union bound. Each test may have a different revealed prefix. -/
theorem adaptive_frame_union_tail {α : Type*} [Fintype α]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (e : ι → E) (he : Orthonormal ℝ e)
    (κ : α → Type*) [∀ r, Fintype (κ r)]
    (a : ∀ r, κ r → ι) (ha : ∀ r, Function.Injective (a r))
    (j : α → ι) (hj : ∀ r k, a r k ≠ j r)
    (q : ∀ r, Ω × (κ r → E) → E) (hq : ∀ r, Measurable (q r))
    {D : ℕ} (hD : ∀ r, D ≤ Module.finrank ℝ E - Fintype.card (κ r))
    {R t : ℝ} (hR : 0 < R) (ht : 0 < t) :
    (μ.prod (haarLaw E)).real {p | ∃ r,
      ‖q r (p.1, fun k => isometry E p.2 (e (a r k)))‖ ≤ R ∧
      t ≤ |⟪q r (p.1, fun k => isometry E p.2 (e (a r k))),
        isometry E p.2 (e (j r))⟫_ℝ|} ≤
      (Fintype.card α : ℝ) * (2 * Real.exp (-(D : ℝ) * t ^ 2 / (2 * R ^ 2))) := by
  let s : α → Set (Ω × Rotation E) := fun r => {p |
      ‖q r (p.1, fun k => isometry E p.2 (e (a r k)))‖ ≤ R ∧
      t ≤ |⟪q r (p.1, fun k => isometry E p.2 (e (a r k))),
        isometry E p.2 (e (j r))⟫_ℝ|}
  have hevent : {p | ∃ r, p ∈ s r} = ⋃ r, s r := by ext; simp
  change (μ.prod (haarLaw E)).real {p | ∃ r, p ∈ s r} ≤ _
  rw [hevent]
  apply (measureReal_iUnion_fintype_le s).trans
  calc
    _ ≤ ∑ _r : α, 2 * Real.exp (-(D : ℝ) * t ^ 2 / (2 * R ^ 2)) := by
      apply Finset.sum_le_sum
      intro r _
      apply (coin_query_inside_tail μ e he (a r) (ha r) (j r) (hj r) (q r) (hq r) hR ht).trans
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.exp_le_exp.mpr
      have hd : (D : ℝ) ≤ (Module.finrank ℝ E - Fintype.card (κ r) : ℕ) := by
        exact_mod_cast hD r
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right (neg_le_neg hd) (sq_nonneg t)
    _ = _ := by simp

theorem spherical_union_confidence (m D : ℕ) {R t δ : ℝ}
    (hR : 0 < R) (hδ : 0 < δ)
    (hdim : 2 * R ^ 2 * Real.log (2 * (m : ℝ) / δ) ≤ (D : ℝ) * t ^ 2) :
    (m : ℝ) * (2 * Real.exp (-(D : ℝ) * t ^ 2 / (2 * R ^ 2))) ≤ δ := by
  by_cases hm : m = 0
  · simpa [hm] using hδ.le
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hden : 0 < 2 * R ^ 2 := by positivity
  have hratio : 0 < 2 * (m : ℝ) / δ := by positivity
  have he : -(D : ℝ) * t ^ 2 / (2 * R ^ 2) ≤ -Real.log (2 * (m : ℝ) / δ) := by
    apply (div_le_iff₀ hden).mpr
    nlinarith only [hdim]
  calc
    _ ≤ (m : ℝ) * (2 * Real.exp (-Real.log (2 * (m : ℝ) / δ))) := by gcongr
    _ = δ := by rw [Real.exp_neg, Real.exp_log hratio]; field_simp; ring

end SampleReuse.RandomFrame
