import Bilevel.SourceFrameActions

/-! A frozen finite query batch before each actual source action. The source
memory and success counter change only at the last observation subround.
Thus enlarging this batch changes the observation dimension, not the number
of source oracle calls. -/
noncomputable section
open MeasureTheory
universe u
namespace Bilevel.SourceFrameActions
open EuclideanGaussian ProjectionPosterior TransportControllerMachine

variable {H : Memory.{u}} {d T B : ℕ}

def batchRules (L : Rules H d T) (hB : 0 < B)
    (queries : ℕ → H → Fin B → Space d)
    (hq : ∀ t k, Measurable (fun h => queries t h k)) : Rules H d T where
  first t h := queries (t/B) h ⟨t%B,Nat.mod_lt _ hB⟩
  first_measurable t := hq (t/B) _
  second _ _ := 0
  second_measurable _ := measurable_const
  request t h := if t%B+1=B then L.request (t/B) h else false
  request_measurable t := by
    by_cases ht : t%B+1=B
    · simpa only [if_pos ht] using L.request_measurable (t/B)
    · simp only [if_neg ht]; exact measurable_const
  column t h := L.column (t/B) h
  column_measurable t := L.column_measurable (t/B)
  finish t p := if t%B+1=B then L.finish (t/B) p else p.1
  finish_measurable t := by
    by_cases ht : t%B+1=B
    · simpa only [if_pos ht] using L.finish_measurable (t/B)
    · simp only [if_neg ht]; exact measurable_fst
  output := L.output
  output_measurable := L.output_measurable

theorem batch_step_before (L : Rules H d T) (hB : 0 < B)
    (queries : ℕ → H → Fin B → Space d)
    (hq : ∀ t k, Measurable (fun h => queries t h k))
    (t r : ℕ) (hr : r+1 < B) (h : H) (U : Frame d T) :
    step (batchRules L hB queries hq) (t*B+r) h U = h := by
  have hm : (t*B+r)%B = r := by simp [Nat.add_mod,Nat.mod_eq_of_lt (show r<B by omega)]
  simp only [step,batchRules,hm,if_neg (by omega : ¬r+1=B)]

theorem batch_step_last (L : Rules H d T) (hB : 0 < B)
    (queries : ℕ → H → Fin B → Space d)
    (hq : ∀ t k, Measurable (fun h => queries t h k))
    (t : ℕ) (h : H) (U : Frame d T) :
    step (batchRules L hB queries hq) (t*B+(B-1)) h U = step L t h U := by
  have hm : (t*B+(B-1))%B = B-1 := by simp [Nat.add_mod,Nat.mod_eq_of_lt (show B-1<B by omega)]
  have hd : (t*B+(B-1))/B = t := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hB]
    simp [Nat.div_eq_of_lt (show B-1<B by omega)]
  simp only [step,batchRules,hm,hd,if_pos (by omega : B-1+1=B)]

theorem run_add (L : Rules H d T) (n m t : ℕ) (h : H) (U : Frame d T) :
    run L (n+m) t h U = run L m (t+n) (run L n t h U) U := by
  induction n generalizing t h with
  | zero => simp only [Nat.zero_add,Nat.add_zero,run]
  | succ n ih =>
    rw [Nat.succ_add,run,ih,run]
    congr 1
    omega

theorem batch_run_before (L : Rules H d T) (hB : 0 < B)
    (queries : ℕ → H → Fin B → Space d)
    (hq : ∀ t k, Measurable (fun h => queries t h k)) :
    ∀ n t r (h : H) (U : Frame d T), r+n < B →
      run (batchRules L hB queries hq) n (t*B+r) h U = h := by
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro t r h U hr
    rw [run,batch_step_before L hB queries hq t r (by omega)]
    convert ih t (r+1) h U (by omega) using 1

theorem batch_run_one (L : Rules H d T) (hB : 0 < B)
    (queries : ℕ → H → Fin B → Space d)
    (hq : ∀ t k, Measurable (fun h => queries t h k))
    (t : ℕ) (h : H) (U : Frame d T) :
    run (batchRules L hB queries hq) B (t*B) h U = step L t h U := by
  have hb : B=(B-1)+1 := by omega
  conv_lhs => arg 2; rw [hb]
  rw [run_add]
  have hp := batch_run_before L hB queries hq (B-1) t 0 h U (by omega)
  simp only [Nat.zero_add,Nat.add_zero] at hp
  rw [hp]
  simpa only [run] using batch_step_last L hB queries hq t h U

theorem batch_run_blocks (L : Rules H d T) (hB : 0 < B)
    (queries : ℕ → H → Fin B → Space d)
    (hq : ∀ t k, Measurable (fun h => queries t h k)) :
    ∀ n t (h : H) (U : Frame d T),
      run (batchRules L hB queries hq) (n*B) (t*B) h U = run L n t h U := by
  intro n
  induction n with
  | zero => intros; simp only [Nat.zero_mul,run]
  | succ n ih =>
    intro t h U
    rw [Nat.succ_mul,Nat.add_comm (n*B) B,run_add,batch_run_one]
    have ht : t*B+B=(t+1)*B := by ring
    rw [ht,ih,run]

theorem compiled_batch_run_memory (L : Rules H d T) (hB : 0 < B)
    (queries : ℕ → H → Fin B → Space d)
    (hq : ∀ t k, Measurable (fun h => queries t h k))
    (n R t : ℕ) (h : H) (V : Submodule ℝ (Space d)) (S : Set (Fin T))
    (U : Frame d T) (hR : n*B ≤ R) :
    (OrdinaryFrame.run (compileRules (batchRules L hB queries hq)) (n*B) R (t*B)
      ((h,false),(V,S)) U).1 = (run L n t h U,false) := by
  rw [compiled_run_memory _ _ _ _ _ _ _ _ hR,batch_run_blocks]

end Bilevel.SourceFrameActions
