import GradientHessian.AugmentedNumericalPostprocessor
import GradientHessian.NumericalSourceCaches

/-! The augmented compiler's actual charged prior cache and supplied target
cache. The readout prelude preserves the suspended cursor, so the first
policy initialization uses the complete initial disclosure packet. -/

noncomputable section
namespace GradientHessian.AugmentedNumericalCaches
open Classical HigherHierarchy HierarchyAddresses FrontierState TaskState
  NumericalCachedOracle AugmentedNumericalDriver

variable {d n r J ell : ℕ} {E : Type} {H : ℕ → Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [∀ h,MeasurableSpace (H h)] [∀ h,BorelSpace (H h)] [∀ h,FiniteDimensional ℝ (H h)]
variable {Seed S : Type*} [MeasurableSpace Seed] [MeasurableSpace S]
variable (t : ℕ)
variable [MeasurableSpace (DirectionPolicyReplay.Point d J E H t)]
  [BorelSpace (DirectionPolicyReplay.Point d J E H t)]
  [MeasurableSpace (DirectionPolicyReplay.Ordinary d J E H t)]
  [BorelSpace (DirectionPolicyReplay.Ordinary d J E H t)]
  [MeasurableSpace (DirectionPolicyReplay.Rich d J E H t)]
  [BorelSpace (DirectionPolicyReplay.Rich d J E H t)]
local notation "Run" => AugmentedNumericalPreprocessor.RuntimeState (d := d) (n := n) (r := r)
  (J := J) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t

variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ)
  (leaf : Leaf (t+1))

def filled (j : Fin (4096*J^2+1)) (readout : (Fin d → ℝ) → Fin d → ℝ) (k : ℕ) (s : Run) : Run :=
  (s.1,(fun q => if q.val<k then true else s.2.1.1 q,
    fun q => if q.val<k then NumericalPriorCache.value B j readout s.1.1 q else s.2.1.2 q),s.2.2)

def loaded (j : Fin (4096*J^2+1)) (readout : (Fin d → ℝ) → Fin d → ℝ)
    (w : RawNumericalExperiment.Auxiliary d n r J E H t Seed) : Run :=
  (w,NumericalPriorCache.store B j readout w.1,Sum.inl PUnit.unit)

theorem filled_write (j : Fin (4096*J^2+1)) (readout : (Fin d → ℝ) → Fin d → ℝ)
    (k : ℕ) (hk : k<4096*J^2+1) (s : Run) :
    filled t B j readout k (AugmentedNumericalPreprocessor.write t k
      (s,readout (AugmentedNumericalPreprocessor.mark t B j k s)))=filled t B j readout (k+1) s := by
  simp only [filled,AugmentedNumericalPreprocessor.write,AugmentedNumericalPreprocessor.mark,
    dif_pos hk,NumericalPriorCache.value]
  congr 1
  apply Prod.ext
  · apply Prod.ext
    · exact NumericalPreloadRuntime.fill_update (fun _ => true) s.2.1.1 k hk
    · exact NumericalPreloadRuntime.fill_update (fun q => (NumericalOrdinaryProcedure.coordinates d).symm
        (readout (NumericalOrdinaryProcedure.coordinates d
          (LowRank.matrixEuclideanMap B (NumericalPreprocessor.marks j s.1.1 q))))) s.2.1.2 k hk
  · rfl

theorem prepared_exact (j : Fin (4096*J^2+1)) (readout : (Fin d → ℝ) → Fin d → ℝ)
    (k : ℕ) (hk : k≤4096*J^2+1) (s : Run) :
    DisclosurePreload.prepared (AugmentedNumericalPreprocessor.mark t B j)
      (AugmentedNumericalPreprocessor.write t) readout k s=filled t B j readout k s := by
  induction k generalizing s with
  | zero => simp [DisclosurePreload.prepared,filled]
  | succ k ih =>
      rw [DisclosurePreload.prepared,ih (by omega)]
      exact filled_write t B j readout k (by omega) s

theorem prepared_initial (j : Fin (4096*J^2+1)) (readout : (Fin d → ℝ) → Fin d → ℝ)
    (w : RawNumericalExperiment.Auxiliary d n r J E H t Seed) :
    DisclosurePreload.prepared (AugmentedNumericalPreprocessor.mark t B j)
      (AugmentedNumericalPreprocessor.write t) readout j.val
      (AugmentedNumericalPreprocessor.initial (ell := ell) (S := S) t w)=loaded t B j readout w := by
  rw [prepared_exact t B j readout j.val (Nat.le_of_lt j.isLt)]
  simp only [filled,loaded,AugmentedNumericalPreprocessor.initial,NumericalPriorCache.store]
  congr 1

theorem loaded_cache (j : Fin (4096*J^2+1)) (x : RawHierarchy.Raw d n r J E H t × Seed) :
    AugmentedNumericalPreprocessor.cache t B j
      (loaded (ell := ell) (S := S) t B j
        (ForkMachineBound.earlierReadout J P fallback (NumericalSourceCaches.input t leaf j x))
        (NumericalSourceCaches.input t leaf j x).1.2)=NumericalSourceCaches.preCache P B fallback t leaf j x := rfl

theorem post_loaded_cache (j : Fin (4096*J^2+1)) (x : RawHierarchy.Raw d n r J E H t × Seed) :
    AugmentedNumericalPostprocessor.cache t B j (AugmentedNumericalPostprocessor.initial t
      (loaded (ell := ell) (S := S) t B j
        (ForkMachineBound.earlierReadout J P fallback (NumericalSourceCaches.input t leaf j x))
        (NumericalSourceCaches.input t leaf j x).1.2) (NumericalSourceCaches.input t leaf j x).2.1)=
      NumericalSourceCaches.postCache P B fallback t leaf j x := rfl

theorem pre_packet (K : ℝ) (j : Fin (4096*J^2+1)) (x : RawHierarchy.Raw d n r J E H t × Seed)
    (s : State (t+1) (4096*J^2+1) ell) (hs : AugmentedDisclosure.markStop leaf j s=false) :
    AugmentedNumericalPacket.packet P B fallback t leaf K
      (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x.1).2
      (NumericalSourceCaches.preCache P B fallback t leaf j x) s=
        AugmentedDisclosure.view K (RawHierarchy.assemble P B fallback t x.1) s :=
  AugmentedNumericalPacket.packet_before_supply P B fallback t leaf K x.1 _ j s hs
    (fun k hk => NumericalSourceCaches.pre_forcing P B fallback t leaf j k x hk)
    (fun k hk => NumericalSourceCaches.pre_readout P B fallback t leaf j k x hk)

theorem post_packet (K : ℝ) (j : Fin (4096*J^2+1)) (x : RawHierarchy.Raw d n r J E H t × Seed)
    (s : State (t+1) (4096*J^2+1) ell) (hs : ComparisonControllerReplay.taskDisclosed leaf j s=false) :
    AugmentedNumericalPacket.packet P B fallback t leaf K
      (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x.1).2
      (NumericalSourceCaches.postCache P B fallback t leaf j x) s=
        AugmentedDisclosure.view K (RawHierarchy.assemble P B fallback t x.1) s :=
  AugmentedNumericalPacket.packet_before_disclosure P B fallback t leaf K x.1 _ j s hs
    (fun k _ => congrFun (NumericalSourceCaches.post_forcing P B fallback t leaf j x) k)
    (fun k hk => NumericalSourceCaches.post_readout P B fallback t leaf j k x hk)

end GradientHessian.AugmentedNumericalCaches
