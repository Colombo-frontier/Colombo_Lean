import SecondOrder.CappedInformationCost
import SecondOrder.FiniteEventInformation

open MeasureTheory InformationTheory
open scoped Classical ENNReal

universe u v

namespace SecondOrder
noncomputable section
variable {S A : Type u} [Fintype S] [Fintype A]

/-- The entire joint reply transcript, including an arbitrary continuous
response or output map, inherits the capped information bound. -/
theorem cappedAdaptiveResponse_kl (p : PMF S)
    (select : ∀ n, FiniteHistory S A n → Bool) (cap : ℕ)
    (K L D : ∀ n, FiniteHistory S A n → PMF A)
    (hp : ∀ s, p s≠0) (hK : ∀ n h a, K n h a≠0)
    (hL : ∀ n h a, L n h a≠0) (hD : ∀ n h a, D n h a≠0)
    {κ : ℝ} (hκ : 0≤κ)
    (hKL : ∀ n h, pmfKL (K n h) (L n h)≤ if select n h=true then κ else 0)
    (n : ℕ) [MeasurableSpace (FiniteHistory S A n)] [MeasurableSingletonClass (FiniteHistory S A n)]
    {B : Type v} [MeasurableSpace B] [MeasurableSingletonClass B] (Φ : FiniteHistory S A n → B) :
    klDiv ((finiteAdaptiveLaw p (cappedTransition select cap K D) n).toMeasure.map Φ)
      ((finiteAdaptiveLaw p (cappedTransition select cap L D) n).toMeasure.map Φ)≤ENNReal.ofReal (κ*cap) := by
  have hp' := finiteAdaptiveLaw_ne_zero p (cappedTransition select cap K D) hp
    (cappedTransition_ne_zero select cap K D hK hD) n
  have hq' := finiteAdaptiveLaw_ne_zero p (cappedTransition select cap L D) hp
    (cappedTransition_ne_zero select cap L D hL hD) n
  have hh := klDiv_finite_response _ _ hp' hq' Φ
  rw [klDiv_pmf _ _ hq'] at hh
  exact hh.trans (ENNReal.ofReal_le_ofReal
    (cappedAdaptiveLaw_pmfKL_le p select cap K L D hp hK hL hD hκ hKL n))

/-- The rare-event argument applied to the actual capped adaptive experiment,
retaining the reference event probability as the sole probabilistic input. -/
theorem cappedAdaptiveEvent_probability (p : PMF S)
    (select : ∀ n, FiniteHistory S A n → Bool) (cap : ℕ)
    (K L D : ∀ n, FiniteHistory S A n → PMF A)
    (hp : ∀ s, p s≠0) (hK : ∀ n h a, K n h a≠0)
    (hL : ∀ n h a, L n h a≠0) (hD : ∀ n h a, D n h a≠0)
    {κ B q₀ : ℝ} (hκ : 0≤κ)
    (hKL : ∀ n h, pmfKL (K n h) (L n h)≤ if select n h=true then κ else 0)
    (n : ℕ) (E : FiniteHistory S A n → Bool)
    (hB : 0<B) (hq₀ : 0<q₀) (hq₁ : q₀<1)
    (hrare : pmfEventProbability (finiteAdaptiveLaw p (cappedTransition select cap L D) n) E≤q₀)
    (hlog : B≤Real.log (1/q₀)) :
    pmfEventProbability (finiteAdaptiveLaw p (cappedTransition select cap K D) n) E≤
      (κ*cap+Real.log 2)/B :=
  pmfEventProbability_information_bound _ _
    (finiteAdaptiveLaw_ne_zero p _ hp (cappedTransition_ne_zero select cap K D hK hD) n)
    (finiteAdaptiveLaw_ne_zero p _ hp (cappedTransition_ne_zero select cap L D hL hD) n) E
    (mul_nonneg hκ (Nat.cast_nonneg _))
    (cappedAdaptiveLaw_pmfKL_le p select cap K L D hp hK hL hD hκ hKL n)
    hB hq₀ hq₁ hrare hlog

theorem cappedAdaptiveEvent_one_thirty_second (p : PMF S)
    (select : ∀ n, FiniteHistory S A n → Bool) (cap : ℕ)
    (K L D : ∀ n, FiniteHistory S A n → PMF A)
    (hp : ∀ s, p s≠0) (hK : ∀ n h a, K n h a≠0)
    (hL : ∀ n h a, L n h a≠0) (hD : ∀ n h a, D n h a≠0)
    {κ B q₀ : ℝ} (hκ : 0≤κ)
    (hKL : ∀ n h, pmfKL (K n h) (L n h)≤ if select n h=true then κ else 0)
    (n : ℕ) (E : FiniteHistory S A n → Bool)
    (hB : 0<B) (hq₀ : 0<q₀) (hq₁ : q₀<1)
    (hrare : pmfEventProbability (finiteAdaptiveLaw p (cappedTransition select cap L D) n) E≤q₀)
    (hlog : B≤Real.log (1/q₀)) (hbudget : 32*(κ*cap+Real.log 2)≤B) :
    pmfEventProbability (finiteAdaptiveLaw p (cappedTransition select cap K D) n) E≤1/32 := by
  apply (cappedAdaptiveEvent_probability p select cap K L D hp hK hL hD hκ hKL n E hB hq₀ hq₁ hrare hlog).trans
  apply (div_le_iff₀ hB).2
  linarith only [hbudget]

end
end SecondOrder
