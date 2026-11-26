import Matvec.AdaptiveIteration

/-! Averaging fixed-input success over an independently sampled admissible basis. -/

namespace Matvec
open MeasureTheory
noncomputable section

theorem independent_mixture_success {F Seed : Type*}
    [MeasurableSpace F] [MeasurableSpace Seed]
    (ν : Measure F) [IsProbabilityMeasure ν] (μ : Measure Seed) [IsProbabilityMeasure μ]
    (admiss : F → Prop) (good : F → Seed → Prop)
    (hadmiss : MeasurableSet {f | admiss f})
    (hgood : MeasurableSet {p : F × Seed | good p.1 p.2})
    (η p : ℝ) (_hη : 0 ≤ η) (hp : p ≤ 1)
    (hadmissprob : 1 - η ≤ ν.real {f | admiss f})
    (hsuccess : ∀ f, admiss f → p ≤ μ.real {seed | good f seed}) :
    p - η ≤ (ν.prod μ).real {x | good x.1 x.2} := by
  have hwrapped : MeasurableSet {x : F × Seed | ¬admiss x.1 ∨ good x.1 x.2} :=
    (hadmiss.preimage measurable_fst).compl.union hgood
  have hf (f : F) : μ.real {seed | ¬(¬admiss f ∨ good f seed)} ≤ 1 - p := by
    by_cases ha : admiss f
    · have hs : MeasurableSet {seed | good f seed} :=
        hgood.preimage (measurable_const.prodMk measurable_id)
      have heq : {seed | ¬(¬admiss f ∨ good f seed)} = {seed | good f seed}ᶜ := by
        ext seed; simp [ha]
      rw [heq, measureReal_compl hs, measureReal_univ_eq_one]
      linarith [hsuccess f ha]
    · simpa [ha] using (sub_nonneg.mpr hp)
  have hfresh := fresh_failure_probability μ ν (fun f : F => f) measurable_id
    (fun f seed => ¬admiss f ∨ good f seed) hwrapped (1 - p) (sub_nonneg.mpr hp) hf
  have hbadbasis : (ν.prod μ).real {x : F × Seed | ¬admiss x.1} ≤ η := by
    have heq : {x : F × Seed | ¬admiss x.1} = {f | admiss f}ᶜ ×ˢ Set.univ := by
      ext x; simp
    rw [heq, measureReal_prod_prod, measureReal_univ_eq_one, mul_one,
      measureReal_compl hadmiss, measureReal_univ_eq_one]
    linarith
  have hsub : {x : F × Seed | ¬good x.1 x.2} ⊆
      {x | ¬admiss x.1} ∪ {x | ¬(¬admiss x.1 ∨ good x.1 x.2)} := by
    intro x hx
    by_cases ha : admiss x.1
    · exact Or.inr (by simpa [ha] using hx)
    · exact Or.inl ha
  have hfail := (measureReal_mono (μ := ν.prod μ) hsub).trans
    (measureReal_union_le _ _)
  have heq : {x : F × Seed | ¬good x.1 x.2} = {x | good x.1 x.2}ᶜ := rfl
  rw [heq, measureReal_compl hgood, measureReal_univ_eq_one] at hfail
  linarith

/-- For countable discrete first seeds, measurability of each section is
sufficient. Finite Walsh sign seeds are a special case. -/
theorem countable_mixture_success {F Seed : Type*}
    [MeasurableSpace F] [Countable F] [MeasurableSingletonClass F]
    [MeasurableSpace Seed]
    (ν : Measure F) [IsProbabilityMeasure ν] (μ : Measure Seed) [IsProbabilityMeasure μ]
    (admiss : F → Prop) (good : F → Seed → Prop)
    (hsections : ∀ f, MeasurableSet {seed | good f seed})
    (η p : ℝ) (hη : 0 ≤ η) (hp : p ≤ 1)
    (hadmissprob : 1 - η ≤ ν.real {f | admiss f})
    (hsuccess : ∀ f, admiss f → p ≤ μ.real {seed | good f seed}) :
    p - η ≤ (ν.prod μ).real {x | good x.1 x.2} := by
  have hadmiss : MeasurableSet {f | admiss f} := Set.to_countable _ |>.measurableSet
  have hgood : MeasurableSet {x : F × Seed | good x.1 x.2} := by
    have heq : {x : F × Seed | good x.1 x.2} =
        ⋃ f : F, ({f} ×ˢ {seed | good f seed}) := by
      ext x
      simp
    rw [heq]
    exact MeasurableSet.iUnion (fun f => (measurableSet_singleton f).prod (hsections f))
  exact independent_mixture_success ν μ admiss good hadmiss hgood η p hη hp hadmissprob hsuccess

end
end Matvec
