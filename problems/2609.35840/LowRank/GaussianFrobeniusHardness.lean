import LowRank.StoppingPosteriorOverlap
import LowRank.FrobeniusHardInstance

/-! For p = 2, the actual Gaussian hard input is hard for measurable stopping
two-sided policies, conditional only on the still-unproved spectral event
probability. No posterior or deferred-decision hypothesis is required here. -/

namespace LowRank
open Matrix MeasureTheory
noncomputable section

def wishartSpectralEvent (d t : ℕ) (L c₀ k : ℝ) : Set (Matrix (Fin d) (Fin t) ℝ) :=
  {X | LoewnerLE (wishart X) ((L / 2) • 1) ∧
    LoewnerLE ((c₀ * (k / d) ^ 2) • (1 - leftKernelProjector X)) (wishart X)}

def boundedFrobeniusSuccess (r s n : ℕ) (L ε : ℝ) {S : Type*} [MeasurableSpace S]
    (policy : BoundedTwoSidedPolicy (r + n) (Matrix (Fin (r + n)) (Fin (r + n)) ℝ) n S) :
    Set (S × Matrix (Fin (r + n)) (Fin (s + n)) ℝ) :=
  {p | frobeniusSq (hardMatrix L (wishart p.2) * (1 - runBoundedHard r s n L policy p)) ≤
    (1 + ε) ^ 2 * frobeniusSq (hardMatrix L (wishart p.2) * (1 - leftKernelProjector p.2))}

theorem gaussian_frobenius_success_le_of_spectral_probability (k s n : ℕ) (L c₀ ε : ℝ)
    {S : Type*} [MeasurableSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    (policy : BoundedTwoSidedPolicy (k + s + n)
      (Matrix (Fin (k + s + n)) (Fin (k + s + n)) ℝ) n S)
    (hk : 0 < k) (hL : 0 < L) (hc : 0 < c₀) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hout : policy.Outputs (k + s + n) (fun P => IsOrthogonalProjector P ∧ P.rank = k) n)
    (hn : (n : ℝ) ≤ (k + s + n : ℝ) / 100) (hkd : (k : ℝ) ≤ (k + s + n : ℝ) / 100)
    (hsmall : (2 * L / c₀) * ε * (k + s + n : ℝ) ^ 3 ≤ (k : ℝ) ^ 3 / 4)
    (hbad : (ν.prod (gaussianMatrixLaw (k + s + n) (s + n))).real
      {p | p.2 ∉ wishartSpectralEvent (k + s + n) (s + n) L c₀ k} ≤ 1 / 20) :
    (ν.prod (gaussianMatrixLaw (k + s + n) (s + n))).real
      (boundedFrobeniusSuccess (k + s) s n L ε policy) ≤ 3 / 20 := by
  let μ := ν.prod (gaussianMatrixLaw (k + s + n) (s + n))
  let E : Set (S × Matrix (Fin (k + s + n)) (Fin (s + n)) ℝ) :=
    {p | p.2 ∈ wishartSpectralEvent (k + s + n) (s + n) L c₀ k}
  let T : Set (S × Matrix (Fin (k + s + n)) (Fin (s + n)) ℝ) :=
    {p | 3 * (k : ℝ) / 4 ≤ (runBoundedHard (k + s) s n L policy p * leftKernelProjector p.2).trace}
  have hout' : policy.Outputs (k + s + n) (fun P => IsOrthogonalProjector P ∧ P.rank ≤ k) n :=
    BoundedTwoSidedPolicy.Outputs.mono (k + s + n) n policy hout
    (fun _ h => ⟨h.1, h.2.le⟩)
  have hT : μ.real T ≤ 1 / 10 :=
    gaussianMatrixLaw_boundedHard_overlap_tail_constant k s n L ν policy hk hout' hn hkd
  have hspec : ∀ᵐ p ∂μ,
      leftKernelProjector p.2 * wishart p.2 = 0 ∧ (leftKernelProjector p.2).trace = (k : ℝ) := by
    have hX := gaussianMatrixLaw_kernel_projector_spec_ae (k + s + n) (s + n) (by omega) (by omega)
    have hp := (Measure.quasiMeasurePreserving_snd (μ := ν)).ae hX
    filter_upwards [hp] with p hp
    refine ⟨hp.2.1, ?_⟩
    simpa only [show k + s + n - (s + n) = k by omega] using hp.2.2.1
  have hsub : ∀ᵐ p ∂μ, p ∈ boundedFrobeniusSuccess (k + s) s n L ε policy → p ∈ Eᶜ ∪ T := by
    filter_upwards [hspec] with p hp
    intro hsuccess
    by_cases he : p ∈ E
    · apply Or.inr
      have hP := runBoundedTwoSided_property (k + s + n) n policy _ hout
        (hardMatrix L (wishart p.2)) p.1
      have htr : (runBoundedHard (k + s) s n L policy p).trace = (k : ℝ) := by
        unfold runBoundedHard
        rw [hP.1.trace_eq_rank, hP.2]
      have hdef := frobenius_hard_instance_overlap hL hc
        (by exact_mod_cast hk) (by exact_mod_cast (show 0 < k + s + n by omega))
        (wishart_posSemidef p.2) hP.1 (leftKernelProjector_isProjector p.2)
        htr hp.2 hp.1 he.1 he.2 hε hε1 hsuccess
      apply overlap_of_cubic_smallness (by exact_mod_cast hk) hdef
      simpa only [Nat.cast_add] using hsmall
    · exact Or.inl he
  have hle : μ.real (boundedFrobeniusSuccess (k + s) s n L ε policy) ≤ μ.real (Eᶜ ∪ T) :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
  have hu := measureReal_union_le (μ := μ) Eᶜ T
  have hb : μ.real Eᶜ ≤ 1 / 20 := hbad
  linarith

end
end LowRank
