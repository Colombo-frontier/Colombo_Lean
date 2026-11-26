import AdaptiveSphereIsotropy

open MeasureTheory Set

namespace Task006.AdaptiveSphere
noncomputable section
variable {W : Type*} [mW : MeasurableSpace W] {μ : Measure W} [IsProbabilityMeasure μ]

/-- Conditional isotropy plus a unit-energy bound gives the per-direction
variance upper bound needed in the stopped-rank argument. No conditional
terminal energy bound is among the premises. -/
theorem conditional_square_le_inverse_dimension
    (n : ℕ) (hn : 0 < n) (m : MeasurableSpace W) (hm : m ≤ mW)
    (X : Fin n → W → ℝ) (hX : ∀ i, Integrable (fun w => (X i w)^2) μ)
    (hsum : (fun w => ∑ i : Fin n, (X i w)^2) ≤ᵐ[μ] (fun _ => 1))
    (hpair : ∀ i l : Fin n, μ[(fun w => (X i w)^2) | m] =ᵐ[μ]
      μ[(fun w => (X l w)^2) | m]) (i : Fin n) :
    μ[(fun w => (X i w)^2) | m] ≤ᵐ[μ] (fun _ => 1/(n:ℝ)) := by
  letI : MeasurableSpace W := mW
  have hsumint : Integrable (fun w => ∑ l : Fin n, (X l w)^2) μ := by
    exact integrable_finset_sum _ (fun l _ => hX l)
  have hmono := condExp_mono (m := m) hsumint (integrable_const (1:ℝ)) hsum
  rw [condExp_const hm (1:ℝ)] at hmono
  have hcesum := condExp_finsetSum (s := Finset.univ)
    (f := fun l : Fin n => fun w => (X l w)^2) (fun l _ => hX l) m
  have hsumfun : (∑ l : Fin n, fun w => (X l w)^2) =
      (fun w => ∑ l : Fin n, (X l w)^2) := by
    funext w
    simp only [Finset.sum_apply]
  rw [hsumfun] at hcesum
  have hall : ∀ᵐ w ∂μ, ∀ l : Fin n,
      (μ[(fun w => (X l w)^2) | m]) w = (μ[(fun w => (X i w)^2) | m]) w := by
    rw [ae_all_iff]
    exact fun l => hpair l i
  filter_upwards [hmono,hcesum,hall] with w hle hs heq
  have hsumw : (∑ l : Fin n, (μ[(fun w => (X l w)^2) | m]) w) ≤ 1 := by
    have hs' : (μ[(fun w => ∑ l : Fin n, (X l w)^2) | m]) w =
        ∑ l : Fin n, (μ[(fun w => (X l w)^2) | m]) w := by
      simpa only [Finset.sum_apply] using hs
    exact hs' ▸ hle
  have hconst : (∑ l : Fin n, (μ[(fun w => (X l w)^2) | m]) w) =
      (n:ℝ)*(μ[(fun w => (X i w)^2) | m]) w := by
    calc
      _ = ∑ _l : Fin n, (μ[(fun w => (X i w)^2) | m]) w :=
        Finset.sum_congr rfl (fun l _ => heq l)
      _ = _ := by simp
  rw [hconst] at hsumw
  apply (le_div_iff₀ (by exact_mod_cast hn : (0:ℝ)<n)).2
  nlinarith

#print axioms conditional_square_le_inverse_dimension
end
end Task006.AdaptiveSphere
