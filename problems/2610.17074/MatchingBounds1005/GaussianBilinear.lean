import MatchingBounds1005.GaussianMatrix

/-! # Uniform projected Gaussian matrix bounds

Two actual finite nets and scalar Gaussian Chernoff estimates give an
exponential operator bound, uniformly over all test vectors.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace BigOperators
open MatchingBounds1005.GaussianVector MatchingBounds1005.GaussianNets
open MatchingBounds1005.GaussianMatrix

namespace MatchingBounds1005.GaussianBilinear

theorem norm_bound_of_inner_net {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s : Finset E) (hnet : ∀ x : E, ‖x‖ = 1 → ∃ y ∈ s, ‖x - y‖ < (1 : ℝ) / 8)
    (x : E) {r : ℝ} (hr : 0 ≤ r) (hb : ∀ y ∈ s, |⟪y, x⟫_ℝ| ≤ r) :
    ‖x‖ ≤ (8 / 7 : ℝ) * r := by
  by_cases hx : x = 0
  · simp only [hx, norm_zero]
    positivity
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let u : E := ‖x‖⁻¹ • x
  have hu : ‖u‖ = 1 := by
    simp only [u, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
  have hi : ⟪u, x⟫_ℝ = ‖x‖ := by
    simp only [u, real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp
    ring
  obtain ⟨y, hy, hxy⟩ := hnet u hu
  have hh := real_inner_le_norm (u - y) x
  rw [inner_sub_left, hi] at hh
  have hmul := mul_le_mul_of_nonneg_right hxy.le hn.le
  have hby := (le_abs_self ⟪y, x⟫_ℝ).trans (hb y hy)
  linarith

theorem opNorm_bound_of_two_nets {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (T : E →L[ℝ] F) (s : Finset E) (t : Finset F)
    (hs : ∀ x : E, ‖x‖ = 1 → ∃ y ∈ s, ‖x - y‖ < (1 : ℝ) / 8)
    (ht : ∀ x : F, ‖x‖ = 1 → ∃ y ∈ t, ‖x - y‖ < (1 : ℝ) / 8)
    {r : ℝ} (hr : 0 ≤ r) (hb : ∀ u ∈ s, ∀ v ∈ t, |⟪v, T u⟫_ℝ| ≤ r) :
    ‖T‖ ≤ 2 * r := by
  have hpoint (u : E) (hu : u ∈ s) : ‖T u‖ ≤ (8 / 7 : ℝ) * r :=
    norm_bound_of_inner_net t ht (T u) hr (hb u hu)
  have hop : ‖T‖ ≤ (8 / 7 : ℝ) * r + ‖T‖ / 8 := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hs x hx
    calc
      ‖T x‖ = ‖T y + T (x - y)‖ := by rw [← map_add, add_sub_cancel]
      _ ≤ ‖T y‖ + ‖T (x - y)‖ := norm_add_le _ _
      _ ≤ (8 / 7 : ℝ) * r + ‖T‖ * ‖x - y‖ := add_le_add (hpoint y hy) (T.le_opNorm _)
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hxy.le (norm_nonneg T)]
  linarith

theorem bilinear_tail {d k m : ℕ} (B : Vec d →L[ℝ] Vec m) (hB : ‖B‖ ≤ 1)
    (u : Vec k) (hu : ‖u‖ = 1) (v : Vec m) (hv : ‖v‖ = 1)
    {r : ℝ} (hr : 0 ≤ r) :
    (gaussianMatrixLaw d k).real {a | r ≤ |⟪v, B (synthesis a u)⟫_ℝ|} ≤
      2 * Real.exp (-r ^ 2 / 2) := by
  have ha : ‖B.adjoint v‖ ≤ 1 := by
    have h := B.adjoint.le_opNorm v
    simpa only [ContinuousLinearMap.adjoint.norm_map, hv, mul_one] using h.trans
      (mul_le_mul_of_nonneg_right (by simpa using hB : ‖B.adjoint‖ ≤ 1) (norm_nonneg v))
  have h := inner_absolute_tail (B.adjoint v) ha hr
  have hp := unit_synthesis_preserving (d := d) u hu
  have hs : MeasurableSet {x : Vec d | r ≤ |⟪B.adjoint v, x⟫_ℝ|} := by
    apply measurableSet_le measurable_const
    fun_prop
  rw [← hp.measureReal_preimage hs.nullMeasurableSet] at h
  simpa only [Set.preimage_setOf_eq, ContinuousLinearMap.adjoint_inner_left] using h

/-- Uniform operator estimate for the actual Gaussian matrix followed by
any fixed linear contraction. The output dimension enters only the net
cardinality, not a polynomial prefactor in the tail exponent. -/
theorem projected_operator_tail {d k m : ℕ} (B : Vec d →L[ℝ] Vec m) (hB : ‖B‖ ≤ 1)
    {r : ℝ} (hr : 0 ≤ r) :
    (gaussianMatrixLaw d k).real {a | 2 * r < ‖B.comp (synthesis a)‖} ≤
      (17 : ℝ) ^ (k + m) * (2 * Real.exp (-r ^ 2 / 2)) := by
  classical
  obtain ⟨s, hscard, hsunit, hsnet⟩ := spectral_sphere_net (E := Vec k)
  obtain ⟨t, htcard, htunit, htnet⟩ := spectral_sphere_net (E := Vec m)
  let bad (uv : Vec k × Vec m) : Set (Fin k → Vec d) :=
    {a | r ≤ |⟪uv.2, B (synthesis a uv.1)⟫_ℝ|}
  have hsub : {a : Fin k → Vec d | 2 * r < ‖B.comp (synthesis a)‖} ⊆
      ⋃ uv ∈ s ×ˢ t, bad uv := by
    intro a ha
    by_contra hn
    have hb : ∀ u ∈ s, ∀ v ∈ t, |⟪v, (B.comp (synthesis a)) u⟫_ℝ| ≤ r := by
      intro u hu v hv
      have hnu : a ∉ bad (u, v) := fun h => hn
        (Set.mem_iUnion.mpr ⟨(u, v), Set.mem_iUnion.mpr ⟨Finset.mem_product.mpr ⟨hu, hv⟩, h⟩⟩)
      exact (lt_of_not_ge hnu).le
    exact (not_lt_of_ge (opNorm_bound_of_two_nets _ s t hsnet htnet hr hb)) ha
  have hcard : ((s ×ˢ t).card : ℝ) ≤ (17 : ℝ) ^ (k + m) := by
    have hs : s.card ≤ 17 ^ k := by simpa using hscard
    have ht : t.card ≤ 17 ^ m := by simpa using htcard
    have hh := Nat.mul_le_mul hs ht
    rw [← pow_add, ← Finset.card_product] at hh
    exact_mod_cast hh
  calc
    _ ≤ (gaussianMatrixLaw d k).real (⋃ uv ∈ s ×ˢ t, bad uv) := measureReal_mono hsub
    _ ≤ ∑ uv ∈ s ×ˢ t, (gaussianMatrixLaw d k).real (bad uv) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _uv ∈ s ×ˢ t, 2 * Real.exp (-r ^ 2 / 2) := by
      apply Finset.sum_le_sum
      intro uv huv
      rcases Finset.mem_product.mp huv with ⟨hu, hv⟩
      exact bilinear_tail B hB uv.1 (hsunit uv.1 hu) uv.2 (htunit uv.2 hv) hr
    _ = ((s ×ˢ t).card : ℝ) * (2 * Real.exp (-r ^ 2 / 2)) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)

theorem projected_operator_exponential {d k m : ℕ} (B : Vec d →L[ℝ] Vec m) (hB : ‖B‖ ≤ 1)
    {r s : ℝ} (hr : 0 ≤ r) (hsize : 6 * ((k + m : ℕ) : ℝ) + 2 * s ≤ r ^ 2) :
    (gaussianMatrixLaw d k).real {a | 2 * r < ‖B.comp (synthesis a)‖} ≤
      2 * Real.exp (-s) := by
  apply (projected_operator_tail B hB hr).trans
  have he : (17 : ℝ) = Real.exp (Real.log 17) := (Real.exp_log (by norm_num)).symm
  conv_lhs => rw [he, ← Real.exp_nat_mul]
  have hlog := mul_le_mul_of_nonneg_left log_seventeen_le_three
    (Nat.cast_nonneg (k + m) : (0 : ℝ) ≤ (k + m : ℕ))
  have hx : ((k + m : ℕ) : ℝ) * Real.log 17 + -r ^ 2 / 2 ≤ -s := by linarith
  have hh := Real.exp_le_exp.mpr hx
  rw [Real.exp_add] at hh
  nlinarith

end MatchingBounds1005.GaussianBilinear
