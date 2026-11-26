import GradientHessian.AugmentedNumericalPreExecution
import GradientHessian.AugmentedNumericalCaches
import GradientHessian.DisclosureCapTransparency

/-! Actual preprocessing uses at most M*ell+1 matrix products and exactly
the charged j prior readouts. The literal caps therefore preserve its run. -/

noncomputable section
namespace GradientHessian.AugmentedNumericalPreBounds
open Classical Matrix HigherHierarchy HierarchyAddresses FrontierState TaskState TaskSlots
  NumericalCachedOracle AugmentedNumericalPreprocessor AugmentedNumericalDriver
  AugmentedNumericalExecution AugmentedNumericalSupplyEquality AugmentedNumericalPreExecution
  AugmentedNumericalCaches

variable {d n r J ell : ℕ} {E : Type} {H : ℕ → Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [∀ h,MeasurableSpace (H h)] [∀ h,BorelSpace (H h)] [∀ h,FiniteDimensional ℝ (H h)]
variable {Seed S : Type*} [MeasurableSpace Seed] [MeasurableSpace S]
variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ)
  (t : ℕ) (leaf : Leaf (t+1))
variable [MeasurableSpace (DirectionPolicyReplay.Point d J E H t)] [BorelSpace (DirectionPolicyReplay.Point d J E H t)]
  [MeasurableSpace (DirectionPolicyReplay.Ordinary d J E H t)] [BorelSpace (DirectionPolicyReplay.Ordinary d J E H t)]
  [MeasurableSpace (DirectionPolicyReplay.Rich d J E H t)] [BorelSpace (DirectionPolicyReplay.Rich d J E H t)]
variable (policy : Machine.Policy (Seed × AugmentedPolicy.Packet d J E H t ell) S
  (DirectionPolicyReplay.Point d J E H t)
  (AugmentedPolicy.Ordinary d J E H t ell) (AugmentedPolicy.Rich d J E H t ell))
local notation "Run" => RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
  (E := E) (H := H) (Seed := Seed) (S := S) t

theorem base_mode_ne_three {K : ℝ} (hK : 0<K) (cutoff : ℕ) (j : Fin (4096*J^2+1)) (s : Run) :
    (baseProgram t P B fallback leaf policy hK cutoff j).mode s≠3 := by
  simp only [baseProgram,mode]
  split_ifs <;> decide

theorem base_disclosures {K : ℝ} (hK : 0<K) (cutoff : ℕ) (j : Fin (4096*J^2+1))
    (A : Matrix (Fin d) (Fin d) ℝ) (readout : (Fin d → ℝ) → Fin d → ℝ) (s : Run) (N : ℕ) :
    (baseProgram t P B fallback leaf policy hK cutoff j).disclosures A readout N s=0 := by
  rw [DisclosureCompiler.Program.disclosures_eq_sum]
  apply Finset.sum_eq_zero
  intro i hi
  exact if_neg (base_mode_ne_three P B fallback t leaf policy hK cutoff j _)

theorem base_calls_bound {K : ℝ} (hK : 0<K) (hell : 0<ell) (cutoff : ℕ) (j : Fin (4096*J^2+1))
    (A : Matrix (Fin d) (Fin d) ℝ) (readout : (Fin d → ℝ) → Fin d → ℝ)
    (s : Run) (hq : Ready (state t s.2.2)) (N : ℕ) :
    (baseProgram t P B fallback leaf policy hK cutoff j).ordinaryCalls A readout N s≤(4096*J^2+1)*ell+1 := by
  let f := fullCursor P B fallback t leaf policy K cutoff (fun _ => false)
    s.1.2.2 s.1.2.1 (cache t B j s) A
  let stop := fun q : Cursor (d := d) (J := J) (ell := ell) (E := E) (H := H) (S := S) t =>
    finished t q || AugmentedDisclosure.markStop leaf j (state t q)
  have hb := product_bound P B fallback t leaf policy K cutoff (fun _ => false)
    s.1.2.2 s.1.2.1 (cache t B j s) A hell N s.2.2 hq
  rw [DisclosureCompiler.Program.ordinaryCalls_eq_sum]
  apply le_trans (Finset.sum_le_sum ?_) hb
  intro i hi
  rw [base_iterate]
  change (if (baseProgram t P B fallback leaf policy hK cutoff j).mode
    (s.1,s.2.1,(ExternalHaltIteration.step f stop)^[i] s.2.2)=2 then 1 else 0)≤_
  cases hs : stop ((ExternalHaltIteration.step f stop)^[i] s.2.2) with
  | true =>
    have hm : (baseProgram t P B fallback leaf policy hK cutoff j).mode
        (s.1,s.2.1,(ExternalHaltIteration.step f stop)^[i] s.2.2)=0 := by
      change (if stop ((ExternalHaltIteration.step f stop)^[i] s.2.2) then 0 else _)=0
      simp only [hs,if_true]
    simp [hm]
  | false =>
    have he := ExternalHaltIteration.iterate_eq_of_open f stop s.2.2 i hs
    rw [he]
    have hh : halt t leaf j (s.1,s.2.1,f^[i] s.2.2)=false := by
      change stop (f^[i] s.2.2)=false
      rw [← he]
      exact hs
    change (if (baseProgram t P B fallback leaf policy hK cutoff j).mode
      (s.1,s.2.1,f^[i] s.2.2)=2 then 1 else 0)≤
      if product t leaf (fun _ => false) (f^[i] s.2.2) then 1 else 0
    cases hp : product t leaf (fun _ => false) (f^[i] s.2.2) <;> simp [baseProgram,mode,hh,hp]

theorem preload_calls_bound {K : ℝ} (hK : 0<K) (hell : 0<ell) (cutoff : ℕ) (j : Fin (4096*J^2+1))
    (A : Matrix (Fin d) (Fin d) ℝ) (readout : (Fin d → ℝ) → Fin d → ℝ)
    (s : Run) (hq : Ready (state t s.2.2)) (N : ℕ) :
    (program t P B fallback leaf policy hK cutoff j).ordinaryCalls A readout (j.val+N) (s,j.val)≤(4096*J^2+1)*ell+1 ∧
    (program t P B fallback leaf policy hK cutoff j).disclosures A readout (j.val+N) (s,j.val)=j.val := by
  have hc := DisclosurePreload.calls_prepared (baseProgram t P B fallback leaf policy hK cutoff j)
    (mark t B j) (write t) (mark_measurable t B j) (write_measurable t) A readout j.val N s
  rw [prepared_exact t B j readout j.val (Nat.le_of_lt j.isLt)] at hc
  change (program t P B fallback leaf policy hK cutoff j).ordinaryCalls A readout (j.val+N) (s,j.val)=_ ∧
    (program t P B fallback leaf policy hK cutoff j).disclosures A readout (j.val+N) (s,j.val)=_ at hc
  constructor
  · rw [hc.1]
    exact base_calls_bound P B fallback t leaf policy hK hell cutoff j A readout (filled t B j readout j.val s) hq N
  · rw [hc.2,base_disclosures]
    exact Nat.zero_add _

theorem capped_preload_projects {K : ℝ} (hK : 0<K) (hell : 0<ell) (cutoff : ℕ) (j : Fin (4096*J^2+1))
    (A : Matrix (Fin d) (Fin d) ℝ) (readout : (Fin d → ℝ) → Fin d → ℝ)
    (s : Run) (hq : Ready (state t s.2.2)) (N : ℕ) :
    ((cappedProgram t P B fallback leaf policy hK cutoff j).eval A readout (j.val+N)
      ((s,j.val),(4096*J^2+1)*ell+1,4096*J^2+1)).2.1=
      ((program t P B fallback leaf policy hK cutoff j).eval A readout (j.val+N) (s,j.val)).2 := by
  have hc := preload_calls_bound P B fallback t leaf policy hK hell cutoff j A readout s hq N
  apply DisclosureCappedProgram.eval_projects _ A readout (j.val+N) (s,j.val) _ _ hc.1
  rw [hc.2]
  exact Nat.le_of_lt j.isLt

theorem capped_preload_halted {K : ℝ} (hK : 0<K) (hell : 0<ell) (cutoff : ℕ) (j : Fin (4096*J^2+1))
    (A : Matrix (Fin d) (Fin d) ℝ) (readout : (Fin d → ℝ) → Fin d → ℝ)
    (s : Run) (hq : Ready (state t s.2.2)) (N : ℕ)
    (hh : ((program t P B fallback leaf policy hK cutoff j).eval A readout (j.val+N) (s,j.val)).1=true) :
    ((cappedProgram t P B fallback leaf policy hK cutoff j).eval A readout (j.val+N)
      ((s,j.val),(4096*J^2+1)*ell+1,4096*J^2+1)).1=true := by
  have hc := preload_calls_bound P B fallback t leaf policy hK hell cutoff j A readout s hq N
  apply DisclosureCappedProgram.eval_halted _ A readout (j.val+N) (s,j.val) _ _ hc.1 _ hh
  rw [hc.2]
  exact Nat.le_of_lt j.isLt

end GradientHessian.AugmentedNumericalPreBounds
