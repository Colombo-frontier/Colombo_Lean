import Nonsmooth.Scales

set_option autoImplicit false
namespace Nonsmooth
noncomputable section

/-- Domain-local assumptions; no differentiability and no extension outside the interval. -/
structure IntervalObjective (L μ R : ℝ) (f : ℝ → ℝ) : Prop where
  lipschitz : ∀ x ∈ Set.Icc (-R) R, ∀ y ∈ Set.Icc (-R) R,
    |f x - f y| ≤ L * |x - y|
  strong : StrongConvexOn (Set.Icc (-R) R) μ f

theorem convex_remainder {L μ R : ℝ} {f : ℝ → ℝ} (hf : IntervalObjective L μ R f) :
    ConvexOn ℝ (Set.Icc (-R) R) (fun x => f x - μ / 2 * x ^ 2) := by
  simpa only [Real.norm_eq_abs, sq_abs] using strongConvexOn_iff_convex.mp hf.strong

/-- Lemma diameter-chord, with the endpoint limit proved by arbitrary positive error. -/
theorem diameter_chord {L μ R a b : ℝ} {f : ℝ → ℝ}
    (hf : IntervalObjective L μ R f) (hμ : 0 < μ) (hR : 0 < R)
    (ha : -R < a) (hab : a < b) (hb : b ≤ R) :
    -L + μ * R + μ / 2 * (a + b) ≤ (f b - f a) / (b - a) := by
  let h := fun x => f x - μ / 2 * x ^ 2
  have hc : ConvexOn ℝ (Set.Icc (-R) R) h := convex_remainder hf
  have hbase : -L + μ * R ≤ (h b - h a) / (b - a) := by
    apply le_of_forall_pos_le_add
    intro ε hε
    let δ := min ((a + R) / 2) (ε / μ)
    have hd0 : 0 < δ := lt_min (by linarith) (div_pos hε hμ)
    have hda : δ ≤ (a + R) / 2 := min_le_left _ _
    have hde : μ * δ ≤ ε := by
      have := (le_div_iff₀ hμ).mp (min_le_right ((a + R) / 2) (ε / μ))
      nlinarith
    let s := -R + δ
    have hsa : s < a := by dsimp [s]; linarith
    have hRs : -R < s := by dsimp [s]; linarith
    have hs : s ∈ Set.Icc (-R) R := ⟨hRs.le, by linarith⟩
    have haI : a ∈ Set.Icc (-R) R := ⟨ha.le, by linarith⟩
    have hbI : b ∈ Set.Icc (-R) R := ⟨by linarith, hb⟩
    have hRI : -R ∈ Set.Icc (-R) R := ⟨le_rfl, by linarith⟩
    have hch := (hc.slope_mono_adjacent hRI haI hRs hsa).trans
      (hc.slope_mono_adjacent hs hbI hsa hab)
    have hl := (abs_le.mp (hf.lipschitz s hs (-R) hRI)).1
    rw [abs_of_pos (sub_pos.mpr hRs)] at hl
    have hlow : -L + μ / 2 * (R - s) ≤ (h s - h (-R)) / (s - -R) := by
      apply (le_div_iff₀ (sub_pos.mpr hRs)).mpr
      dsimp [h]
      linear_combination hl
    have := hlow.trans hch
    dsimp [s] at this
    nlinarith [mul_pos hμ hd0]
  have hid : (f b - f a) / (b - a) =
      (h b - h a) / (b - a) + μ / 2 * (a + b) := by
    dsimp [h]
    field_simp [sub_ne_zero.mpr hab.ne']
    <;> ring
  rw [hid]
  linarith

theorem class_boundary_necessary {L μ R : ℝ} {f : ℝ → ℝ}
    (hf : IntervalObjective L μ R f) (hμ : 0 < μ) (hR : 0 < R) : μ * R ≤ L := by
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := min R (ε / μ)
  have hd : 0 < δ := lt_min hR (div_pos hε hμ)
  have hdR : δ ≤ R := min_le_left _ _
  have hde : μ * δ ≤ ε := by
    have := (le_div_iff₀ hμ).mp (min_le_right R (ε / μ))
    nlinarith
  have hc := diameter_chord hf hμ hR (a := R - δ) (b := R)
    (by linarith) (by linarith) le_rfl
  have hl := (abs_le.mp (hf.lipschitz R ⟨by linarith, le_rfl⟩
    (R - δ) ⟨by linarith, by linarith⟩)).2
  rw [abs_of_pos (by linarith : 0 < R - (R - δ))] at hl
  have hu : (f R - f (R - δ)) / (R - (R - δ)) ≤ L :=
    (div_le_iff₀ (by linarith)).mpr hl
  nlinarith [hc.trans hu]

/-- Positive minimizers lie in the claimed radius. Reflection gives negative minimizers. -/
theorem positive_minimizer_localization {L μ R r : ℝ} {f : ℝ → ℝ}
    (hf : IntervalObjective L μ R f) (hμ : 0 < μ) (hR : 0 < R)
    (hr : 0 < r) (hrR : r ≤ R)
    (hmin : ∀ x ∈ Set.Icc (-R) R, f r ≤ f x) :
    r ≤ radius (gap L μ R) μ R := by
  apply le_min hrR
  apply (le_div_iff₀ hμ).mpr
  have hbound : μ * r ≤ L - μ * R := by
    apply le_of_forall_pos_le_add
    intro ε hε
    let δ := min r (ε / μ)
    have hd : 0 < δ := lt_min hr (div_pos hε hμ)
    have hdr : δ ≤ r := min_le_left _ _
    have hde : μ * δ ≤ ε := by
      have := (le_div_iff₀ hμ).mp (min_le_right r (ε / μ))
      nlinarith
    have hc := diameter_chord hf hμ hR (a := r - δ) (b := r)
      (by linarith) (by linarith) hrR
    have hm := hmin (r - δ) ⟨by linarith, by linarith⟩
    have hz : (f r - f (r - δ)) / (r - (r - δ)) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    nlinarith [hc.trans hz]
  simpa [gap, mul_comm] using hbound

theorem center_regret_bound {L μ R r : ℝ} {f : ℝ → ℝ}
    (hf : IntervalObjective L μ R f) (hμ : 0 < μ) (hR : 0 < R)
    (hr : 0 ≤ r) (hrR : r ≤ R) :
    f 0 - f r ≤ energy (gap L μ R) μ R := by
  have hg : 0 ≤ gap L μ R := by
    have := class_boundary_necessary hf hμ hR
    unfold gap
    linarith
  rcases eq_or_lt_of_le hr with h | h
  · subst r
    simpa using energy_nonneg hg hμ hR.le
  · have hc := diameter_chord hf hμ hR (a := 0) (b := r) (by linarith) h hrR
    have hc' := (le_div_iff₀ (by linarith : 0 < r - 0)).mp hc
    have hm := radial_maximizer hg hμ hR.le hr hrR
    unfold gap at *
    nlinarith

end
end Nonsmooth
