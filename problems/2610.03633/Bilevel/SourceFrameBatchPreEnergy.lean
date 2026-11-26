import Bilevel.SourceFrameBatchObservation
import Bilevel.SourceFrameEnergyEvent

/-! Frozen batch control at the last query insertion, before its possible
own-frame reveal. This is the space needed for old-prefix blindness. -/
noncomputable section
open MeasureTheory
universe u
namespace Bilevel.SourceFrameActions
open EuclideanGaussian ProjectionPosterior TransportControllerMachine

variable {H : Memory.{u}} {d T B : ℕ}
variable (L : Rules H d T) (hB : 0<B)
  (queries : ℕ → H → Fin B → Space d)
  (hq : ∀ t k, Measurable (fun h => queries t h k))

def batchPreSpace (t : ℕ) (s : State H d T) (U : Frame d T) :=
  querySpace (batchRules L hB queries hq) (t*B+(B-1))
    (observeRun (batchRules L hB queries hq) (B-1) (t*B) s U)

theorem batch_pre_memory (t : ℕ) (s : State H d T) (U : Frame d T) :
    (observeRun (batchRules L hB queries hq) (B-1) (t*B) s U).1=s.1 := by
  rw [observeRun_memory]
  simpa only [Nat.add_zero] using batch_run_before L hB queries hq (B-1) t 0 s.1 U (by omega)

theorem batch_pre_known (t : ℕ) (s : State H d T) (U : Frame d T) :
    (observeRun (batchRules L hB queries hq) (B-1) (t*B) s U).2.2=s.2.2 := by
  simpa only [Nat.add_zero] using batch_known_before L hB queries hq (B-1) t 0 s U (by omega)

theorem batch_pre_mono (t : ℕ) (s : State H d T) (U : Frame d T) :
    s.2.1 ≤ batchPreSpace L hB queries hq t s U :=
  (observeRun_space_mono _ _ _ _ _).trans (le_sup_of_le_left le_sup_left)

theorem batch_pre_query_mem (t : ℕ) (s : State H d T) (U : Frame d T) (k : Fin B) :
    queries t s.1 k ∈ batchPreSpace L hB queries hq t s U := by
  by_cases hk : k.val=B-1
  · have hmod : (t*B+(B-1))%B=B-1 := by simp [Nat.add_mod,Nat.mod_eq_of_lt (show B-1<B by omega)]
    have hdiv : (t*B+(B-1))/B=t := by
      rw [Nat.add_comm,Nat.add_mul_div_right _ _ hB]
      simp [Nat.div_eq_of_lt (show B-1<B by omega)]
    have he : (⟨(t*B+(B-1))%B,Nat.mod_lt _ hB⟩ : Fin B)=k := Fin.ext (hmod.trans hk.symm)
    unfold batchPreSpace querySpace
    apply Submodule.mem_sup_left
    apply Submodule.mem_sup_right
    apply Submodule.subset_span
    rw [Set.mem_singleton_iff]
    rw [batch_pre_memory]
    simp only [batchRules,hdiv,he]
  · have h := observeRun_first_mem (batchRules L hB queries hq) (B-1) (t*B) s U k.val (by omega)
    rw [observeRun_memory] at h
    have hm := batch_run_before L hB queries hq k.val t 0 s.1 U (by simp)
    simp only [Nat.add_zero] at hm
    rw [hm] at h
    have hmod : (t*B+k.val)%B=k.val := by simp [Nat.add_mod,Nat.mod_eq_of_lt k.isLt]
    have hdiv : (t*B+k.val)/B=t := by
      rw [Nat.add_comm,Nat.add_mul_div_right _ _ hB]
      simp [Nat.div_eq_of_lt k.isLt]
    have hh : queries t s.1 k ∈ (observeRun (batchRules L hB queries hq) (B-1) (t*B) s U).2.1 := by
      simpa only [batchRules,hmod,hdiv] using h
    exact Submodule.mem_sup_left (Submodule.mem_sup_left hh)

theorem batch_pre_energy_at_call (N j : ℕ) (hj : j<N) (s : State H d T) (U : Frame d T) (cap : ℝ)
    (hgood : SourceObserved (batchRules L hB queries hq) cap (N*B) 0 s U) :
    let a := observeRun (batchRules L hB queries hq) (j*B) 0 s U
    GenieProtocol.BoundedEnergy (batchPreSpace L hB queries hq j a U) a.2.2 U cap := by
  have hm : (j+1)*B≤N*B := Nat.mul_le_mul_right B (by omega)
  have hd : (j+1)*B=j*B+B := by ring
  have hi : j*B+(B-1)<N*B := by omega
  have h := source_observed_at (batchRules L hB queries hq) cap (j*B+(B-1)) (N*B) 0 s U hi hgood
  have he := observeRun_add (batchRules L hB queries hq) (j*B) (B-1) 0 s U
  simp only [Nat.zero_add] at h he
  rw [he,batch_pre_known] at h
  exact h

end Bilevel.SourceFrameActions
