import Bilevel.SourceFrameBatchActions
import Bilevel.SourceFrameObservation

/-! Every frozen batch vector belongs to the actual accumulated observation
space. The batch preserves the exact named-column set of one source step. -/
noncomputable section
open MeasureTheory
universe u
namespace Bilevel.SourceFrameActions
open EuclideanGaussian ProjectionPosterior TransportControllerMachine

variable {H : Memory.{u}} {d T B : ℕ}
variable (L : Rules H d T) (hB : 0 < B)
  (queries : ℕ → H → Fin B → Space d)
  (hq : ∀ t k, Measurable (fun h => queries t h k))

theorem batch_query_mem (t : ℕ) (s : State H d T) (U : Frame d T) (k : Fin B) :
    queries t s.1 k ∈ (observeRun (batchRules L hB queries hq) B (t*B) s U).2.1 := by
  have h := observeRun_first_mem (batchRules L hB queries hq) B (t*B) s U k.val k.isLt
  rw [observeRun_memory] at h
  have hm := batch_run_before L hB queries hq k.val t 0 s.1 U (by simp)
  simp only [Nat.add_zero] at hm
  rw [hm] at h
  have hmod : (t*B+k.val)%B=k.val := by simp [Nat.add_mod,Nat.mod_eq_of_lt k.isLt]
  have hdiv : (t*B+k.val)/B=t := by
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ hB]
    simp [Nat.div_eq_of_lt k.isLt]
  simpa only [batchRules,hmod,hdiv] using h

theorem batch_span_le (t : ℕ) (s : State H d T) (U : Frame d T) :
    Submodule.span ℝ (Set.range (queries t s.1)) ≤
      (observeRun (batchRules L hB queries hq) B (t*B) s U).2.1 := by
  apply Submodule.span_le.mpr
  rintro _ ⟨k,rfl⟩
  exact batch_query_mem L hB queries hq t s U k

theorem batch_known_before : ∀ n t r (s : State H d T) (U : Frame d T), r+n<B →
    (observeRun (batchRules L hB queries hq) n (t*B+r) s U).2.2=s.2.2 := by
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro t r s U hr
    rw [observeRun]
    have ht : t*B+r+1=t*B+(r+1) := by omega
    rw [ht,ih t (r+1)]
    · have hm : (t*B+r)%B=r := by simp [Nat.add_mod,Nat.mod_eq_of_lt (show r<B by omega)]
      simp only [observeStep,batchRules,hm,if_neg (by omega : ¬r+1=B),Bool.false_eq_true,if_false]
    · omega

theorem batch_known_one (t : ℕ) (s : State H d T) (U : Frame d T) :
    (observeRun (batchRules L hB queries hq) B (t*B) s U).2.2 =
      (observeStep L t s U).2.2 := by
  have hb : B=(B-1)+1 := by omega
  have he := observeRun_add (batchRules L hB queries hq) (B-1) 1 (t*B) s U
  rw [←hb] at he
  rw [he]
  have hm := batch_run_before L hB queries hq (B-1) t 0 s.1 U (by omega)
  have hk := batch_known_before L hB queries hq (B-1) t 0 s U (by omega)
  simp only [Nat.add_zero] at hm hk
  have hmod : (t*B+(B-1))%B=B-1 := by simp [Nat.add_mod,Nat.mod_eq_of_lt (show B-1<B by omega)]
  have hdiv : (t*B+(B-1))/B=t := by
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ hB]
    simp [Nat.div_eq_of_lt (show B-1<B by omega)]
  have ha := (observeRun_memory (batchRules L hB queries hq) (B-1) (t*B) s U).trans hm
  change (observeStep (batchRules L hB queries hq) (t*B+(B-1))
    (observeRun (batchRules L hB queries hq) (B-1) (t*B) s U) U).2.2 = _
  simp only [observeStep,ha,hk]
  simp only [batchRules,hmod,hdiv,if_pos (by omega : B-1+1=B)]
  split <;> rfl

end Bilevel.SourceFrameActions
