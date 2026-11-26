import HeavyTail.MaskedCoordinateLaw

/-! The actual one-coordinate importance-weighted response sampler is measurable,
unbiased, and identical for neighboring signs whenever their differing coordinate
is not revealed. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal InnerProductSpace
namespace HeavyTail.MaskedLower
noncomputable section

def coordinateReply {k : ℕ} (π : ℝ) (g : HardSpace k) : CoordinateMask k → HardSpace k
  | none => 0
  | some j => EuclideanSpace.single j (g j / π)

theorem coordinateReply_measurable {k : ℕ} (π : ℝ) :
    Measurable (fun ω : HardSpace k × CoordinateMask k => coordinateReply π ω.1 ω.2) := by
  apply measurable_from_prod_countable
  intro b
  cases b with
  | none => exact measurable_const
  | some j =>
    apply (PiLp.continuous_equiv_symm (p := 2) (β := fun _ : Fin k => ℝ)).measurable.comp
    apply measurable_pi_iff.mpr
    intro i
    by_cases hi : i = j
    · simpa only [coordinateReply, EuclideanSpace.single, Pi.single_apply, if_pos hi] using
        (EuclideanSpace.proj j).continuous.measurable.div_const π
    · simpa only [coordinateReply, EuclideanSpace.single, Pi.single_apply, if_neg hi] using
        (measurable_const : Measurable (fun _ : HardSpace k => (0 : ℝ)))

theorem coordinateReply_unbiased {k : ℕ} {π : ℝ} (hπ : 0 < π)
    (hkπ : (k : ℝ) * π ≤ 1) (g : HardSpace k) :
    (∫ b, coordinateReply π g b ∂(coordinateCoin π hπ.le hkπ).toMeasure) = g := by
  rw [coordinate_expectation]
  simp only [coordinateReply, smul_zero, zero_add]
  apply PiLp.ext
  intro i
  change (EuclideanSpace.proj i) (∑ j : Fin k, π • EuclideanSpace.single j (g j / π)) = g i
  rw [map_sum]
  simp [EuclideanSpace.single_apply, hπ.ne']
  field_simp [hπ.ne']

def maskedSampler {k : ℕ} (a ρ π : ℝ) (v : Fin k → Bool)
    (ω : HardSpace k × CoordinateMask k) : HardSpace k :=
  coordinateReply π (hardGradient a ρ (gaussianSigns v) ω.1) ω.2

theorem maskedSampler_measurable {k : ℕ} (a ρ π : ℝ) (v : Fin k → Bool) :
    Measurable (maskedSampler a ρ π v) :=
  (coordinateReply_measurable π).comp
    (((hardGradient_measurable a ρ (gaussianSigns v)).comp measurable_fst).prodMk measurable_snd)

theorem maskedSampler_neighbor_agreement {k : ℕ} (a ρ π : ℝ) (v : Fin k → Bool)
    (j : Fin k) (x : HardSpace k) (b : CoordinateMask k) (hb : b ≠ some j) :
    maskedSampler a ρ π v (x, b) = maskedSampler a ρ π (gaussianFlip v j) (x, b) := by
  cases b with
  | none => rfl
  | some i =>
    have hij : i ≠ j := fun he => hb (congrArg Option.some he)
    simp only [maskedSampler, coordinateReply]
    rw [gaussian_neighbor_gradient_agrees a ρ v j i hij x]

def maskedKernel {k : ℕ} (a ρ π : ℝ) (hπ : 0 ≤ π) (hkπ : (k : ℝ) * π ≤ 1)
    (v : Fin k → Bool) : Kernel (HardSpace k) (HardSpace k) :=
  kernelOfSampler (coordinateCoin π hπ hkπ).toMeasure (maskedSampler a ρ π v)
    (maskedSampler_measurable a ρ π v)

instance maskedKernel_markov {k : ℕ} (a ρ π : ℝ) (hπ : 0 ≤ π)
    (hkπ : (k : ℝ) * π ≤ 1) (v : Fin k → Bool) :
    IsMarkovKernel (maskedKernel a ρ π hπ hkπ v) := by
  unfold maskedKernel
  infer_instance

end
end HeavyTail.MaskedLower
