import RandomizedFO2003.Model

namespace RandomizedFO2003.Model

open MeasureTheory

def historyPrefix {d t T : ℕ} (ht : t ≤ T) (h : Fin T → Response d) : Fin t → Response d :=
  fun i => h ⟨i.val, lt_of_lt_of_le i.isLt ht⟩

theorem measurable_historyPrefix {d t T : ℕ} (ht : t ≤ T) :
    Measurable (historyPrefix (d := d) ht) :=
  measurable_pi_lambda _ (fun _ => measurable_pi_apply _)

theorem transcript_prefix {d : ℕ} {Seed : Type} [MeasurableSpace Seed]
    (A : Algorithm d Seed) (f : Space d → ℝ) (seed : Seed) {t T : ℕ} (ht : t ≤ T) :
    historyPrefix ht (transcript A f seed T) = transcript A f seed t := by
  induction T generalizing t with
  | zero =>
    have he : t = 0 := by omega
    subst t
    rfl
  | succ T ih =>
    by_cases he : t = T + 1
    · subst t; rfl
    · have ht' : t ≤ T := by omega
      calc
        _ = historyPrefix ht' (transcript A f seed T) := by
          funext i
          change transcript A f seed (T + 1) (⟨i.val, lt_of_lt_of_le i.isLt ht'⟩ : Fin T).castSucc = _
          simp only [transcript, Fin.snoc_castSucc, historyPrefix]
        _ = _ := ih ht'

/-- Pad an algorithm with zero queries, while retaining its output at the
original horizon. This establishes monotonicity of exact query budgets. -/
def Algorithm.pad {d : ℕ} {Seed : Type} [MeasurableSpace Seed]
    (A : Algorithm d Seed) (S : ℕ) : Algorithm d Seed where
  query t seed h := if t < S then A.query t seed h else 0
  output t seed h := if ht : S ≤ t then A.output S seed (historyPrefix ht h) else A.output t seed h
  query_measurable t := by
    by_cases ht : t < S
    · simpa only [if_pos ht] using A.query_measurable t
    · simpa only [if_neg ht] using
        (measurable_const : Measurable (fun _ : Seed × (Fin t → Response d) => (0 : Space d)))
  output_measurable t := by
    by_cases ht : S ≤ t
    · simpa only [dif_pos ht] using (A.output_measurable S).comp
        (measurable_fst.prodMk ((measurable_historyPrefix ht).comp measurable_snd))
    · simpa only [dif_neg ht] using A.output_measurable t

theorem Algorithm.pad_transcript {d : ℕ} {Seed : Type} [MeasurableSpace Seed]
    (A : Algorithm d Seed) (S : ℕ) (f : Space d → ℝ) (seed : Seed) (t : ℕ) (ht : t ≤ S) :
    transcript (A.pad S) f seed t = transcript A f seed t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hlt : t < S := by omega
    have hq : (A.pad S).query t = A.query t := by
      funext seed h
      simp only [Algorithm.pad, if_pos hlt]
    simp only [transcript, hq, ih (by omega)]

theorem Algorithm.pad_output {d : ℕ} {Seed : Type} [MeasurableSpace Seed]
    (A : Algorithm d Seed) (S T : ℕ) (hST : S ≤ T) (f : Space d → ℝ) (seed : Seed) :
    (A.pad S).output T seed (transcript (A.pad S) f seed T) =
      A.output S seed (transcript A f seed S) := by
  change (if ht : S ≤ T then A.output S seed (historyPrefix ht _) else _) = _
  rw [dif_pos hST, transcript_prefix, A.pad_transcript S f seed S le_rfl]

theorem Algorithm.pad_success {d : ℕ} {Seed : Type} [MeasurableSpace Seed]
    (A : Algorithm d Seed) (S T : ℕ) (hST : S ≤ T) (f : Space d → ℝ) (ε : ℝ) :
    Success (A.pad S) f ε T = Success A f ε S := by
  ext seed
  simp only [Success, Set.mem_setOf_eq, A.pad_output S T hST]

end RandomizedFO2003.Model
