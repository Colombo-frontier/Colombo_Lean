import AdaptiveSphereConditionalBound

open MeasureTheory Set
open scoped Matrix RealInnerProductSpace

namespace Task006.AdaptiveSphere
noncomputable section
variable {W : Type*} [mW : MeasurableSpace W] {μ : Measure W} [IsProbabilityMeasure μ]

/-- Exact conditional isotropic energy, with pairwise equality established
independently by genuine transformations. -/
theorem conditional_square_eq_div_of_pair
    (n : ℕ) (hn : 0 < n) (m : MeasurableSpace W) (hm : m ≤ mW)
    (X : Fin n → W → ℝ) (hX : ∀ i, Integrable (fun w => (X i w)^2) μ)
    (Y : W → ℝ) (hY : Integrable Y μ) (hYm : StronglyMeasurable[m] Y)
    (hsum : (fun w => ∑ i : Fin n, (X i w)^2) =ᵐ[μ] Y)
    (hpair : ∀ i l : Fin n, μ[(fun w => (X i w)^2) | m] =ᵐ[μ]
      μ[(fun w => (X l w)^2) | m]) (i : Fin n) :
    μ[(fun w => (X i w)^2) | m] =ᵐ[μ] (fun w => Y w/(n:ℝ)) := by
  letI : MeasurableSpace W := mW
  have hcesum := condExp_finsetSum (s := Finset.univ)
    (f := fun l : Fin n => fun w => (X l w)^2) (fun l _ => hX l) m
  have hsumfun : (∑ l : Fin n, fun w => (X l w)^2) =
      (fun w => ∑ l : Fin n, (X l w)^2) := by
    funext w
    simp only [Finset.sum_apply]
  rw [hsumfun] at hcesum
  have hceY := (condExp_congr_ae (μ := μ) (m := m) hsum).trans
    (Filter.EventuallyEq.of_eq (condExp_of_stronglyMeasurable hm hYm hY))
  have hall : ∀ᵐ w ∂μ, ∀ l : Fin n,
      (μ[(fun w => (X l w)^2) | m]) w = (μ[(fun w => (X i w)^2) | m]) w := by
    rw [ae_all_iff]
    exact fun l => hpair l i
  filter_upwards [hceY,hcesum,hall] with w hy hs heq
  have hsumw : (∑ l : Fin n, (μ[(fun w => (X l w)^2) | m]) w) = Y w := by
    simpa only [Finset.sum_apply] using hs.symm.trans hy
  have hconst : (∑ l : Fin n, (μ[(fun w => (X l w)^2) | m]) w) =
      (n:ℝ)*(μ[(fun w => (X i w)^2) | m]) w := by
    calc
      _ = ∑ _l : Fin n, (μ[(fun w => (X i w)^2) | m]) w :=
        Finset.sum_congr rfl (fun l _ => heq l)
      _ = _ := by simp
  rw [hconst] at hsumw
  apply (eq_div_iff (by exact_mod_cast (ne_of_gt hn) : (n:ℝ)≠0)).2
  nlinarith

#print axioms conditional_square_eq_div_of_pair
end
end Task006.AdaptiveSphere
