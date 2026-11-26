import LowRank.SchattenHardInstance
import LowRank.SchattenSuccessEvent

/-! General positive-p relative Schatten success on the actual Gaussian
hard distribution has probability at most 3/20, conditional only on the
explicit Wishart spectral probability estimate. -/

namespace LowRank
open Matrix MeasureTheory
noncomputable section

theorem exists_gaussian_schatten_success_bound {p L c₀ : ℝ}
    (hp : 0 < p) (hL : 0 < L) (hc : 0 < c₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k s n : ℕ) (ε : ℝ)
      {S : Type*} [MeasurableSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
      (policy : BoundedTwoSidedPolicy (k + s + n)
        (Matrix (Fin (k + s + n)) (Fin (k + s + n)) ℝ) n S),
      0 < k → 0 ≤ ε → ε ≤ 1 →
      policy.Outputs (k + s + n) (fun P => IsOrthogonalProjector P ∧ P.rank = k) n →
      (n : ℝ) ≤ (k + s + n : ℝ) / 100 → (k : ℝ) ≤ (k + s + n : ℝ) / 100 →
      C * ε * (k + s + n : ℝ) ^ 3 ≤ (k : ℝ) ^ 3 / 4 →
      (ν.prod (gaussianMatrixLaw (k + s + n) (s + n))).real
        {z | z.2 ∉ wishartSpectralEvent (k + s + n) (s + n) L c₀ k} ≤ 1 / 20 →
      (ν.prod (gaussianMatrixLaw (k + s + n) (s + n))).real
        (boundedOptimalSchattenSuccess (k + s) s n k p L ε policy) ≤ 3 / 20 := by
  obtain ⟨C, hC, hdet⟩ := exists_schatten_hard_instance_overlap hp hL hc
  refine ⟨C, hC, ?_⟩
  intro k s n ε S _ ν _ policy hk hε hε1 hout hn hkd hsmall hbad
  let μ := ν.prod (gaussianMatrixLaw (k + s + n) (s + n))
  let E : Set (S × Matrix (Fin (k + s + n)) (Fin (s + n)) ℝ) :=
    {z | z.2 ∈ wishartSpectralEvent (k + s + n) (s + n) L c₀ k}
  let T : Set (S × Matrix (Fin (k + s + n)) (Fin (s + n)) ℝ) :=
    {z | 3 * (k : ℝ) / 4 ≤ (runBoundedHard (k + s) s n L policy z * leftKernelProjector z.2).trace}
  have hout' : policy.Outputs (k + s + n) (fun P => IsOrthogonalProjector P ∧ P.rank ≤ k) n :=
    BoundedTwoSidedPolicy.Outputs.mono (k + s + n) n policy hout
      (fun _ h => ⟨h.1, h.2.le⟩)
  have hT : μ.real T ≤ 1 / 10 :=
    gaussianMatrixLaw_boundedHard_overlap_tail_constant k s n L ν policy hk hout' hn hkd
  have hspec : ∀ᵐ z ∂μ,
      leftKernelProjector z.2 * wishart z.2 = 0 ∧ (leftKernelProjector z.2).rank = k := by
    have hX := gaussianMatrixLaw_kernel_projector_spec_ae (k + s + n) (s + n) (by omega) (by omega)
    have hz := (Measure.quasiMeasurePreserving_snd (μ := ν)).ae hX
    filter_upwards [hz] with z hz
    refine ⟨hz.2.1, ?_⟩
    rw [hz.2.2.2]
    omega
  have hsub : ∀ᵐ z ∂μ, z ∈ boundedOptimalSchattenSuccess (k + s) s n k p L ε policy →
      z ∈ Eᶜ ∪ T := by
    filter_upwards [hspec] with z hz
    intro hsuccess
    by_cases he : z ∈ E
    · apply Or.inr
      have hP := runBoundedTwoSided_property (k + s + n) n policy _ hout
        (hardMatrix L (wishart z.2)) z.1
      have hdef := hdet (by omega) hk (wishart_posSemidef z.2) hP.1 (leftKernelProjector_isProjector z.2)
        hP.2 hz.2 hz.1 he.1 he.2 hε hε1 hsuccess
      apply overlap_of_cubic_smallness (by exact_mod_cast hk) hdef
      simpa only [Nat.cast_add] using hsmall
    · exact Or.inl he
  have hle : μ.real (boundedOptimalSchattenSuccess (k + s) s n k p L ε policy) ≤
      μ.real (Eᶜ ∪ T) :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
  have hu := measureReal_union_le (μ := μ) Eᶜ T
  have hb : μ.real Eᶜ ≤ 1 / 20 := hbad
  linarith

end
end LowRank
