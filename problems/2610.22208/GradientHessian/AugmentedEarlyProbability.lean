import GradientHessian.AugmentedNumericalProbability
import GradientHessian.AugmentedEarlyExpectation

noncomputable section
namespace GradientHessian.AugmentedEarlyPhase
open Classical MeasureTheory Matrix LowRank HigherHierarchy RawHierarchy FrontierState TaskState
  GeometricRepair AugmentedPolicy
open DirectionPolicyReplay (Point)

variable {d n r J ell : ℕ} {E : Type} {H : ℕ → Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [∀ h,MeasurableSpace (H h)] [∀ h,BorelSpace (H h)] [∀ h,FiniteDimensional ℝ (H h)]
variable [∀ t,MeasurableSpace (Point d J E H t)] [∀ t,BorelSpace (Point d J E H t)]
  [∀ t,MeasurableSpace (DirectionPolicyReplay.Ordinary d J E H t)] [∀ t,BorelSpace (DirectionPolicyReplay.Ordinary d J E H t)]
  [∀ t,MeasurableSpace (DirectionPolicyReplay.Rich d J E H t)] [∀ t,BorelSpace (DirectionPolicyReplay.Rich d J E H t)]
variable {Seed S : Type*} [MeasurableSpace Seed] [MeasurableSpace S]
variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ)
  (t : ℕ) (policy : Machine.Policy (Seed × Packet d J E H t ell) S (Point d J E H t)
    (Ordinary d J E H t ell) (Rich d J E H t ell))
variable (σ : Measure Seed) [IsProbabilityMeasure σ]
variable [IsProbabilityMeasure (ConditionedSource.sourceLaw (n := n) P J)]

theorem early_probability_of_containment (κ : ℕ) (hJ : ForkLifetime.depthThreshold≤J)
    (hr : ForkLifetime.rankRatio*((4096*J^2+1:ℕ):ℝ)≤r) (hκ : 18874368≤κ)
    (hd : d=κ*r*J) (hn : n+κ*r=d)
    (hP : IsOrthogonalProjector P) (hrank : P.rank=r) (hB : Bᵀ*B=1) (hPB : P*B=B)
    (hell : ell=ForkLifetime.lifetime J) {K : ℝ} (hK : 0<K)
    (leaf : Leaf (t+1)) (j : Fin (4096*J^2+1)) (N : ℕ)
    (hcontain : ∀ᵐ w ∂(RawHierarchy.law (n := n) P t).prod σ,
      w∈earlyEvent P B fallback t policy K N leaf j →
      w∈AugmentedNumericalProbability.rawEvent P B fallback t leaf policy hK j N) :
    ((RawHierarchy.law (n := n) P t).prod σ).real
      (earlyEvent P B fallback t policy K N leaf j)≤1/256 := by
  letI := RawHierarchy.law_probability (n := n) (r := r) (J := J) (E := E) (H := H) P t
  have hm := measure_mono_ae hcontain
  have hm' := ENNReal.toReal_mono (measure_ne_top _ _) hm
  exact hm'.trans (AugmentedNumericalProbability.raw_probability P B fallback t leaf policy σ κ
    hJ hr hκ hd hn hP hrank hB hPB hell hK j N)

theorem early_mean_of_containment (κ : ℕ) (hJ : ForkLifetime.depthThreshold≤J)
    (hr : ForkLifetime.rankRatio*((4096*J^2+1:ℕ):ℝ)≤r) (hκ : 18874368≤κ)
    (hd : d=κ*r*J) (hn : n+κ*r=d)
    (hP : IsOrthogonalProjector P) (hrank : P.rank=r) (hB : Bᵀ*B=1) (hPB : P*B=B)
    (hell : ell=ForkLifetime.lifetime J) (hellpos : 0<ell) {K : ℝ} (hK : 0<K) (N : ℕ)
    (hcontain : ∀ (leaf : Leaf (t+1)) (j : Fin (4096*J^2+1)),
      ∀ᵐ w ∂(RawHierarchy.law (n := n) P t).prod σ,
      w∈earlyEvent P B fallback t policy K N leaf j →
      w∈AugmentedNumericalProbability.rawEvent P B fallback t leaf policy hK j N) :
    (∫ w,(earlyCount P B fallback t policy K N w : ℝ)
      ∂(RawHierarchy.law (n := n) P t).prod σ)≤(8:ℝ)^(t+1)*(4096*J^2+1)/256 := by
  letI := RawHierarchy.law_probability (n := n) (r := r) (J := J) (E := E) (H := H) P t
  apply early_mean_le_inventory_fraction P B fallback t policy _ hK N hellpos
  intro leaf j
  exact early_probability_of_containment P B fallback t policy σ κ hJ hr hκ hd hn
    hP hrank hB hPB hell hK leaf j N (hcontain leaf j)

end GradientHessian.AugmentedEarlyPhase
