import GradientHessian.AugmentedNumericalPreBounds
import GradientHessian.AugmentedNumericalForkPrograms

/-! Exact saved runtime at target supply, including suspended initial
mark supply. The actual capped fork program preserves both saved state
and halt flag; all previous readouts are charged before this execution. -/

noncomputable section
universe u v w
namespace GradientHessian.AugmentedNumericalPreTransparency
open Classical Matrix HigherHierarchy HierarchyAddresses FrontierState TaskState TaskSlots
  NumericalCachedOracle AugmentedNumericalPreprocessor AugmentedNumericalDriver
  AugmentedNumericalExecution AugmentedNumericalSupplyEquality AugmentedNumericalPreExecution
  AugmentedNumericalCaches AugmentedNumericalPreBounds

variable {d n r J ell : ℕ} {E : Type} {H : ℕ → Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [∀ h,MeasurableSpace (H h)] [∀ h,BorelSpace (H h)] [∀ h,FiniteDimensional ℝ (H h)]
variable {Seed : Type u} {S : Type v} [MeasurableSpace Seed] [MeasurableSpace S]
variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ)
  (t : ℕ) (leaf : Leaf (t+1))
variable [MeasurableSpace (DirectionPolicyReplay.Point d J E H t)] [BorelSpace (DirectionPolicyReplay.Point d J E H t)]
  [MeasurableSpace (DirectionPolicyReplay.Ordinary d J E H t)] [BorelSpace (DirectionPolicyReplay.Ordinary d J E H t)]
  [MeasurableSpace (DirectionPolicyReplay.Rich d J E H t)] [BorelSpace (DirectionPolicyReplay.Rich d J E H t)]
variable (policy : Machine.Policy (Seed × AugmentedPolicy.Packet d J E H t ell) S
  (DirectionPolicyReplay.Point d J E H t)
  (AugmentedPolicy.Ordinary d J E H t ell) (AugmentedPolicy.Rich d J E H t ell))
def savedRuntime (K : ℝ) (j : Fin (4096*J^2+1)) (A : Matrix (Fin d) (Fin d) ℝ)
    (readout : (Fin d → ℝ) → Fin d → ℝ) (cutoff : ℕ)
    (w : RawNumericalExperiment.Auxiliary d n r J E H t Seed) (N : ℕ) :
    RuntimeState.{u,v,w} (d := d) (n := n) (r := r) (J := J) (ell := ell)
      (E := E) (H := H) (Seed := Seed) (S := S) t :=
  (w,NumericalPriorCache.store B j readout w.1,
    (externalCursor P B fallback t leaf policy K cutoff j w.2.2 w.2.1
      (cache t B j (loaded.{u,v,w} (ell := ell) (S := S) t B j readout w)) A)^[N] (Sum.inl PUnit.unit))

theorem uncapped_eval {K : ℝ} (hK : 0<K) (j : Fin (4096*J^2+1))
    (A : Matrix (Fin d) (Fin d) ℝ) (readout : (Fin d → ℝ) → Fin d → ℝ)
    (cutoff : ℕ) (w : RawNumericalExperiment.Auxiliary d n r J E H t Seed) (N : ℕ) :
    (program t P B fallback leaf policy hK cutoff j).eval A readout (j.val+N)
      (AugmentedNumericalPreprocessor.initial (ell := ell) (S := S) t w,j.val)=
      (((baseProgram.{u,v,w} t P B fallback leaf policy hK cutoff j).eval A readout N
        (loaded.{u,v,w} (ell := ell) (S := S) t B j readout w)).1,
        savedRuntime.{u,v,w} P B fallback t leaf policy K j A readout cutoff w N,0) := by
  have he := DisclosurePreload.eval_prepared (baseProgram t P B fallback leaf policy hK cutoff j)
    (mark t B j) (write t) (mark_measurable t B j) (write_measurable t) A readout j.val N
      (AugmentedNumericalPreprocessor.initial (ell := ell) (S := S) t w)
  rw [prepared_initial t B j readout w] at he
  change (program t P B fallback leaf policy hK cutoff j).eval A readout (j.val+N)
    (AugmentedNumericalPreprocessor.initial (ell := ell) (S := S) t w,j.val)=_ at he
  rw [he,base_eval_state]
  rfl

theorem uncapped_halted {K : ℝ} (hK : 0<K) (j : Fin (4096*J^2+1))
    (A : Matrix (Fin d) (Fin d) ℝ) (readout : (Fin d → ℝ) → Fin d → ℝ)
    (cutoff : ℕ) (w : RawNumericalExperiment.Auxiliary d n r J E H t Seed) (N : ℕ)
    (hh : halt t leaf j (savedRuntime.{u,v,w} P B fallback t leaf policy K j A readout cutoff w N)=true) :
    ((program.{u,v,w} t P B fallback leaf policy hK cutoff j).eval A readout (j.val+N)
      (AugmentedNumericalPreprocessor.initial (ell := ell) (S := S) t w,j.val)).1=true := by
  rw [uncapped_eval.{u,v,w}]
  change ((baseProgram.{u,v,w} t P B fallback leaf policy hK cutoff j).eval A readout N
    (loaded.{u,v,w} (ell := ell) (S := S) t B j readout w)).1=true
  rw [DisclosureCompiler.Program.eval_flag_iterate,base_iterate]
  change (baseProgram.{u,v,w} t P B fallback leaf policy hK cutoff j).mode
    (savedRuntime.{u,v,w} P B fallback t leaf policy K j A readout cutoff w N)=0
  simp [baseProgram,mode,hh]

theorem capped_state {K : ℝ} (hK : 0<K) (hell : 0<ell) (j : Fin (4096*J^2+1))
    (A : Matrix (Fin d) (Fin d) ℝ) (readout : (Fin d → ℝ) → Fin d → ℝ)
    (cutoff : ℕ) (w : RawNumericalExperiment.Auxiliary d n r J E H t Seed) (N : ℕ) :
    ((AugmentedNumericalForkPrograms.pre.{u,v,w} t P B fallback leaf policy hK cutoff j).eval A readout (j.val+N)
      ((AugmentedNumericalForkPrograms.preInitial (d := d) (n := n) (r := r) (J := J) (ell := ell)
        (E := E) (H := H) (Seed := Seed) (S := S) t j ((4096*J^2+1)*ell+1) (4096*J^2+1)).1 w)).2.1=
      (savedRuntime.{u,v,w} P B fallback t leaf policy K j A readout cutoff w N,0) := by
  rw [AugmentedNumericalForkPrograms.pre,AugmentedNumericalForkPrograms.preInitial]
  rw [capped_preload_projects P B fallback t leaf policy hK hell cutoff j A readout
    (AugmentedNumericalPreprocessor.initial (ell := ell) (S := S) t w) (initial_ready hell) N,
    uncapped_eval.{_,_,_}]

theorem capped_halted {K : ℝ} (hK : 0<K) (hell : 0<ell) (j : Fin (4096*J^2+1))
    (A : Matrix (Fin d) (Fin d) ℝ) (readout : (Fin d → ℝ) → Fin d → ℝ)
    (cutoff : ℕ) (w : RawNumericalExperiment.Auxiliary d n r J E H t Seed) (N : ℕ)
    (hh : halt t leaf j (savedRuntime.{u,v,w} P B fallback t leaf policy K j A readout cutoff w N)=true) :
    ((AugmentedNumericalForkPrograms.pre.{u,v,w} t P B fallback leaf policy hK cutoff j).eval A readout (j.val+N)
      ((AugmentedNumericalForkPrograms.preInitial (d := d) (n := n) (r := r) (J := J) (ell := ell)
        (E := E) (H := H) (Seed := Seed) (S := S) t j ((4096*J^2+1)*ell+1) (4096*J^2+1)).1 w)).1=true := by
  exact capped_preload_halted P B fallback t leaf policy hK hell cutoff j A readout
    (AugmentedNumericalPreprocessor.initial (ell := ell) (S := S) t w) (initial_ready hell) N
    (uncapped_halted.{u,v,w} P B fallback t leaf policy hK j A readout cutoff w N hh)

end GradientHessian.AugmentedNumericalPreTransparency
