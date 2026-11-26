import Matvec.SourceIteration
import Matvec.InversePowerSchedule
import Matvec.SpectralBridge

/-!
# Actual randomized power iteration with adaptive inverse applications

The estimator is a measurable finite iteration of a given approximate inverse
routine. Its call inputs are previous random iterates. Uniform guarantees are
transported through those adaptive inputs using an actual product seed law.
-/

namespace Matvec

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

variable {E Seed : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Seed]

def sourcePower (applyInverse : E → Seed → E) (q : ℕ) (g : E)
    (seeds : SeedBlock Seed q) : E :=
  adaptiveRun (fun _ => applyInverse) g q seeds

def sourcePowerEstimate (applyInverse : E → Seed → E) (q : ℕ) (g : E)
    (seeds : SeedBlock Seed q) : ℝ := powerRoot ‖sourcePower applyInverse q g seeds‖ q

def sourcePowerGood (M : E →L[ℝ] E) (applyInverse : E → Seed → E)
    (η : ℝ) (_ : ℕ) (g : E) (seed : Seed) : Prop :=
  ‖applyInverse g seed - M g‖ ≤ η * ‖M‖ * ‖g‖

theorem measurable_sourcePower (applyInverse : E → Seed → E)
    (happly : Measurable (fun p : E × Seed => applyInverse p.1 p.2)) (q : ℕ) :
    Measurable (fun p : E × SeedBlock Seed q => sourcePower applyInverse q p.1 p.2) :=
  measurable_adaptiveRun_initial _ (fun _ => happly) q

theorem measurable_sourcePowerEstimate (applyInverse : E → Seed → E)
    (happly : Measurable (fun p : E × Seed => applyInverse p.1 p.2)) (q : ℕ) :
    Measurable (fun p : E × SeedBlock Seed q => sourcePowerEstimate applyInverse q p.1 p.2) := by
  exact ((measurable_sourcePower applyInverse happly q).norm).pow_const _

theorem measurableSet_sourcePowerGood (M : E →L[ℝ] E) (applyInverse : E → Seed → E)
    (happly : Measurable (fun p : E × Seed => applyInverse p.1 p.2)) (η : ℝ) (n : ℕ) :
    MeasurableSet {p : E × Seed | sourcePowerGood M applyInverse η n p.1 p.2} :=
  measurableSet_le ((happly.sub (M.continuous.measurable.comp measurable_fst)).norm)
    (measurable_const.mul measurable_fst.norm)

theorem sourcePower_failure_probability (μ : Measure Seed) [IsProbabilityMeasure μ]
    (M : E →L[ℝ] E) (applyInverse : E → Seed → E)
    (happly : Measurable (fun p : E × Seed => applyInverse p.1 p.2))
    (η δ : ℝ) (hδ : 0 ≤ δ)
    (hfailure : ∀ g, μ.real {seed | η * ‖M‖ * ‖g‖ < ‖applyInverse g seed - M g‖} ≤ δ)
    (q : ℕ) (g : E) :
    (seedBlockLaw μ q).real
      {seeds | adaptiveFailure (fun _ => applyInverse) (sourcePowerGood M applyInverse η) g q seeds} ≤
      (q : ℝ) * δ := by
  exact adaptive_failure_probability μ _ _ g (fun _ => happly)
    (measurableSet_sourcePowerGood M applyInverse happly η) δ hδ
    (fun _ g => by simpa only [sourcePowerGood, not_le] using hfailure g) q

theorem sourcePower_factor_two (M : E →L[ℝ] E) (applyInverse : E → Seed → E)
    (g v : E) (eigenvalue ν η : ℝ) (d q : ℕ)
    (hν : 0 < ν) (hd : 0 < d) (hq : 0 < q)
    (hsymm : M.toLinearMap.IsSymmetric)
    (heigen : M v = eigenvalue • v) (hv : ‖v‖ = 1) (hM : ‖M‖ ≤ |eigenvalue|)
    (hη : 0 ≤ η) (hg : ‖g‖ ≤ 1)
    (hstart : ν / Real.sqrt d ≤ |⟪v, g⟫_ℝ|)
    (hsmall : (q : ℝ) * η ≤ 1 / 2)
    (haccuracy : η ≤ ν / (8 * (q : ℝ) * Real.sqrt d))
    (hthreshold : 4 * Real.sqrt d / (3 * ν) ≤ (2 : ℝ) ^ q)
    (seeds : SeedBlock Seed q)
    (hgood : ¬adaptiveFailure (fun _ => applyInverse) (sourcePowerGood M applyInverse η) g q seeds) :
    ‖M‖ / 2 ≤ sourcePowerEstimate applyInverse q g seeds ∧
      sourcePowerEstimate applyInverse q g seeds ≤ 2 * ‖M‖ := by
  have heq := top_eigenvalue_eq_opNorm M v eigenvalue heigen hv hM
  let z := adaptiveHistory (fun _ => applyInverse) g q seeds
  have hz0 : z 0 = g := adaptiveHistory_zero _ _ _ _
  have hstep : ∀ n < q, ‖z (n + 1) - M (z n)‖ ≤ η * |eigenvalue| * ‖z n‖ := by
    rw [heq]
    exact adaptiveHistory_good _ (sourcePowerGood M applyInverse η) g
      (fun _ x y => ‖y - M x‖ ≤ η * ‖M‖ * ‖x‖) (fun _ _ _ h => h) q seeds hgood
  have h := inversePower_good_start_estimate M g v z eigenvalue ν η d q hν hd hq
    (fun x y => hsymm x y) heigen hv hM hη hg hz0 hstep hstart hsmall haccuracy hthreshold
  simpa only [heq, z, adaptiveHistory_last, sourcePowerEstimate, sourcePower] using h

theorem sourcePower_upper (M : E →L[ℝ] E) (applyInverse : E → Seed → E)
    (g : E) (η : ℝ) (q : ℕ) (hq : 0 < q) (hη : 0 ≤ η) (hg : ‖g‖ ≤ 1)
    (hsmall : (q : ℝ) * η ≤ 1 / 2) (seeds : SeedBlock Seed q)
    (hgood : ¬adaptiveFailure (fun _ => applyInverse) (sourcePowerGood M applyInverse η) g q seeds) :
    sourcePowerEstimate applyInverse q g seeds ≤ 2 * ‖M‖ := by
  let z := adaptiveHistory (fun _ => applyInverse) g q seeds
  have hstep : ∀ n < q, ‖z (n + 1) - M (z n)‖ ≤ η * ‖M‖ * ‖z n‖ :=
    adaptiveHistory_good _ (sourcePowerGood M applyInverse η) g
      (fun _ x y => ‖y - M x‖ ≤ η * ‖M‖ * ‖x‖) (fun _ _ _ h => h) q seeds hgood
  have h := inversePower_all_start_upper M g z ‖M‖ η (norm_nonneg _) hη le_rfl hg
    (adaptiveHistory_zero _ _ _ _) q hq hstep hsmall
  simpa only [z, adaptiveHistory_last, sourcePowerEstimate, sourcePower] using h

/-- Random starts and all adaptive inverse applications use distinct product
coordinates. The latter fail with probability at most qδ, uniformly in the start. -/
theorem random_sourcePower_calls_failure {Start : Type*} [MeasurableSpace Start]
    (ρ : Measure Start) [IsProbabilityMeasure ρ]
    (start : Start → E) (hstart : Measurable start)
    (μ : Measure Seed) [IsProbabilityMeasure μ]
    (M : E →L[ℝ] E) (applyInverse : E → Seed → E)
    (happly : Measurable (fun p : E × Seed => applyInverse p.1 p.2))
    (η δ : ℝ) (hδ : 0 ≤ δ)
    (hfailure : ∀ g, μ.real {seed | η * ‖M‖ * ‖g‖ < ‖applyInverse g seed - M g‖} ≤ δ)
    (q : ℕ) :
    (ρ.prod (seedBlockLaw μ q)).real
      {p | adaptiveFailure (fun _ => applyInverse) (sourcePowerGood M applyInverse η) (start p.1) q p.2} ≤
      (q : ℝ) * δ := by
  have hm := measurableSet_adaptiveFailure_initial (fun _ => applyInverse)
    (sourcePowerGood M applyInverse η) (fun _ => happly)
    (measurableSet_sourcePowerGood M applyInverse happly η) q
  have h := fresh_failure_probability (seedBlockLaw μ q) ρ start hstart
    (fun g seeds => ¬adaptiveFailure (fun _ => applyInverse)
      (sourcePowerGood M applyInverse η) g q seeds) hm.compl ((q : ℝ) * δ)
    (by positivity) (fun g => by
      simpa only [not_not] using sourcePower_failure_probability μ M applyInverse happly η δ hδ hfailure q g)
  simpa only [not_not] using h

/-- A concrete start sampler and a uniform approximate-inverse guarantee give
a quantitative estimator success probability. A top eigenvector is constructed
by the spectral theorem, rather than assumed to exist. -/
theorem random_sourcePower_probability [FiniteDimensional ℝ E] [Nontrivial E]
    {Start : Type*} [MeasurableSpace Start]
    (ρ : Measure Start) [IsProbabilityMeasure ρ]
    (start : Start → E) (hstart : Measurable start) (hstartnorm : ∀ s, ‖start s‖ ≤ 1)
    (μ : Measure Seed) [IsProbabilityMeasure μ]
    (M : E →L[ℝ] E) (hM : M.toLinearMap.IsSymmetric)
    (applyInverse : E → Seed → E)
    (happly : Measurable (fun p : E × Seed => applyInverse p.1 p.2))
    (ν η δ pgood : ℝ) (d q : ℕ) (hν : 0 < ν) (hd : 0 < d) (hq : 0 < q)
    (hη : 0 ≤ η) (hδ : 0 ≤ δ)
    (hfailure : ∀ g, μ.real {seed | η * ‖M‖ * ‖g‖ < ‖applyInverse g seed - M g‖} ≤ δ)
    (hprojection : ∀ v : E, ‖v‖ = 1 →
      pgood ≤ ρ.real {s | ν / Real.sqrt d ≤ |⟪v, start s⟫_ℝ|})
    (hsmall : (q : ℝ) * η ≤ 1 / 2)
    (haccuracy : η ≤ ν / (8 * (q : ℝ) * Real.sqrt d))
    (hthreshold : 4 * Real.sqrt d / (3 * ν) ≤ (2 : ℝ) ^ q) :
    pgood - (q : ℝ) * δ ≤ (ρ.prod (seedBlockLaw μ q)).real
      {p | ‖M‖ / 2 ≤ sourcePowerEstimate applyInverse q (start p.1) p.2 ∧
        sourcePowerEstimate applyInverse q (start p.1) p.2 ≤ 2 * ‖M‖} ∧
    (ρ.prod (seedBlockLaw μ q)).real
      {p | 2 * ‖M‖ < sourcePowerEstimate applyInverse q (start p.1) p.2} ≤ (q : ℝ) * δ := by
  obtain ⟨eigenvalue, v, hv, heigen, hnorm⟩ := symmetric_top_eigenvector M hM
  let failure : Set (Start × SeedBlock Seed q) :=
    {p | adaptiveFailure (fun _ => applyInverse) (sourcePowerGood M applyInverse η) (start p.1) q p.2}
  let success : Set (Start × SeedBlock Seed q) :=
    {p | ‖M‖ / 2 ≤ sourcePowerEstimate applyInverse q (start p.1) p.2 ∧
      sourcePowerEstimate applyInverse q (start p.1) p.2 ≤ 2 * ‖M‖}
  have hbad : (ρ.prod (seedBlockLaw μ q)).real failure ≤ (q : ℝ) * δ :=
    random_sourcePower_calls_failure ρ start hstart μ M applyInverse happly η δ hδ hfailure q
  constructor
  · have hsub : {s | ν / Real.sqrt d ≤ |⟪v, start s⟫_ℝ|} ×ˢ Set.univ ⊆ success ∪ failure := by
      intro s hs
      by_cases hb : s ∈ failure
      · exact Or.inr hb
      · apply Or.inl
        exact sourcePower_factor_two M applyInverse (start s.1) v eigenvalue ν η d q
          hν hd hq hM heigen hv hnorm hη (hstartnorm s.1) hs.1 hsmall haccuracy hthreshold s.2 hb
    have hg := hprojection v hv
    have hp : pgood ≤ (ρ.prod (seedBlockLaw μ q)).real
        ({s | ν / Real.sqrt d ≤ |⟪v, start s⟫_ℝ|} ×ˢ Set.univ) := by
      simpa only [measureReal_prod_prod, measureReal_univ_eq_one, mul_one] using hg
    have hle := (measureReal_mono (μ := ρ.prod (seedBlockLaw μ q)) hsub).trans
      (measureReal_union_le success failure)
    change pgood - (q : ℝ) * δ ≤ (ρ.prod (seedBlockLaw μ q)).real success
    linarith
  · apply le_trans (measureReal_mono (μ := ρ.prod (seedBlockLaw μ q)) ?_) hbad
    intro s hs
    change s ∈ failure
    by_contra hb
    exact (not_lt_of_ge (sourcePower_upper M applyInverse (start s.1) η q hq hη
      (hstartnorm s.1) hsmall s.2 hb)) hs

end
end Matvec

