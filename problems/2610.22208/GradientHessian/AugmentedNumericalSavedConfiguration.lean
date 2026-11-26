import GradientHessian.AugmentedNumericalPreTransparency
import GradientHessian.AugmentedNumericalSupplyEquality
import GradientHessian.NumericalSourceCaches

noncomputable section
namespace GradientHessian.AugmentedNumericalSavedConfiguration
open Classical Matrix HigherHierarchy HierarchyAddresses FrontierState TaskState TaskSlots
  ComparisonController ComparisonControllerReplay GeometricRepair ControllerNormalRealization NumericalSourceCaches

variable {d n r J ell : ℕ} {E : Type} {H : ℕ → Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [∀ h,MeasurableSpace (H h)] [∀ h,BorelSpace (H h)] [∀ h,FiniteDimensional ℝ (H h)]
variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ)
  (t : ℕ) (leaf : Leaf (t+1))
variable [MeasurableSpace (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)]
  [BorelSpace (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)]
  [MeasurableSpace (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))]
  [BorelSpace (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))]
  [MeasurableSpace (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ) ×
    (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ]
      Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))]
  [BorelSpace (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ) ×
    (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ]
      Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))]
variable {Seed S : Type*} [MeasurableSpace Seed] [MeasurableSpace S]
variable (policy : Machine.Policy (Seed × AugmentedPolicy.Packet d J E H t ell) S
  (DirectionPolicyReplay.Point d J E H t)
  (AugmentedPolicy.Ordinary d J E H t ell) (AugmentedPolicy.Rich d J E H t ell))

theorem saved_config {K : ℝ} (hK : 0<K) (hell : 0<ell)
    (x : RawHierarchy.Raw d n r J E H t × Seed) (N k : ℕ) (j : Fin (4096*J^2+1)) :
    let w := input t leaf j x
    let A := ForkMachineBound.sourceA J P w
    let readout := ForkMachineBound.earlierReadout J P fallback w
    (AugmentedNumericalPreTransparency.savedRuntime P B fallback t leaf policy K j A readout N w.1.2 k).2.2=
      (AugmentedNumericalSupplyEquality.externalCursor P B fallback t leaf policy K N j
        w.1.2.2.2 w.1.2.2.1 (postCache P B fallback t leaf j x) A)^[k] (Sum.inl PUnit.unit) := by
  change (AugmentedNumericalSupplyEquality.externalCursor P B fallback t leaf policy K N j
    (input t leaf j x).1.2.2.2 (input t leaf j x).1.2.2.1 (preCache P B fallback t leaf j x)
    (ForkMachineBound.sourceA J P (input t leaf j x)))^[k] (Sum.inl PUnit.unit)=_
  rw [external_eq t leaf j x,seed_eq t leaf j x,matrix_eq P t leaf j x]
  exact AugmentedNumericalSupplyEquality.initial_caches_eq P B fallback t leaf policy hK hell x.1
    (preCache P B fallback t leaf j x) (postCache P B fallback t leaf j x) j
    (fun q hq => pre_forcing P B fallback t leaf j q x hq)
    (fun q hq => pre_readout P B fallback t leaf j q x hq)
    (fun q _ => congrFun (post_forcing P B fallback t leaf j x) q)
    (fun q hq => post_readout P B fallback t leaf j q x hq) N k x.2

theorem post_saved_cache (K : ℝ) (x : RawHierarchy.Raw d n r J E H t × Seed)
    (N k : ℕ) (j : Fin (4096*J^2+1)) :
    let w := input t leaf j x
    let A := ForkMachineBound.sourceA J P w
    let readout := ForkMachineBound.earlierReadout J P fallback w
    let saved := AugmentedNumericalPreTransparency.savedRuntime P B fallback t leaf policy K j A readout N w.1.2 k
    AugmentedNumericalPostprocessor.cache t B j (AugmentedNumericalPostprocessor.initial t saved w.2.1)=
      postCache P B fallback t leaf j x := rfl

end GradientHessian.AugmentedNumericalSavedConfiguration
