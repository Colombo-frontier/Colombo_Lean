import RandomizedFO2003.ResponseBlock
import RandomizedFO2003.DeterministicMachine

namespace RandomizedFO2003.Accelerated

open MeasureTheory

noncomputable section

/-- Block start, stored gradient responses, and most recent successful output. -/
abbrev BlockState (d : ℕ) := Model.Space d × (ℕ → Model.Space d) × Model.Space d

def blockQuery {d : ℕ} (η θ : ℝ) (N t : ℕ) (s : BlockState d) : Model.Space d :=
  replyQuery η θ s.1 s.2.1 (t % N)

def blockPush {d : ℕ} (r : ℕ) (p : BlockState d × Model.Response d) : BlockState d :=
  (p.1.1, Function.update p.1.2.1 r p.2.2, p.1.2.2)

def blockFinish {d : ℕ} (η θ B : ℝ) (N : ℕ) (s : BlockState d) : BlockState d :=
  (replyRestartPoint η θ B N s.1 s.2.1, fun _ => 0,
    if (N : ℝ) * replyEnergy η θ s.1 s.2.1 N ≤ B ^ 2 then replyOutput η θ N s.1 s.2.1 else s.2.2)

def blockStep {d : ℕ} (η θ B : ℝ) (N t : ℕ) (p : BlockState d × Model.Response d) : BlockState d :=
  let s := blockPush (t % N) p
  if (t + 1) % N = 0 then blockFinish η θ B N s else s

theorem measurable_blockQuery {d : ℕ} (η θ : ℝ) (N t : ℕ) :
    Measurable (blockQuery (d := d) η θ N t) :=
  (measurable_replyQuery η θ (t % N)).comp (measurable_fst.prodMk measurable_snd.fst)

theorem measurable_blockPush {d : ℕ} (r : ℕ) : Measurable (blockPush (d := d) r) :=
  measurable_fst.fst.prodMk
    ((measurable_update'.comp (measurable_fst.snd.fst.prodMk measurable_snd.snd)).prodMk
      measurable_fst.snd.snd)

theorem measurable_blockFinish {d : ℕ} (η θ B : ℝ) (N : ℕ) :
    Measurable (blockFinish (d := d) η θ B N) := by
  have hz : Measurable (fun s : BlockState d => (s.1, s.2.1)) :=
    measurable_fst.prodMk measurable_snd.fst
  have he := (measurable_replyEnergy η θ N).comp hz
  have ho := (measurable_replyOutput η θ N).comp hz
  exact ((measurable_replyRestartPoint η θ B N).comp hz).prodMk
    (measurable_const.prodMk (Measurable.ite (measurableSet_le (measurable_const.mul he)
      measurable_const) ho measurable_snd.snd))

theorem measurable_blockStep {d : ℕ} (η θ B : ℝ) (N t : ℕ) :
    Measurable (blockStep (d := d) η θ B N t) := by
  unfold blockStep
  split_ifs
  · exact (measurable_blockFinish η θ B N).comp (measurable_blockPush (t % N))
  · exact measurable_blockPush (t % N)

/-- A deterministic first-order machine. It never inspects f: only the
gradient components of the supplied responses enter its transition. -/
def acceleratedMachine {d : ℕ} (η θ B : ℝ) (N : ℕ) (initial : Model.Space d) :
    Model.DeterministicMachine d (BlockState d) where
  initial := (initial, fun _ => 0, initial)
  query := blockQuery η θ N
  step := blockStep η θ B N
  output _ s := s.2.2
  measurable_query := measurable_blockQuery η θ N
  measurable_step := measurable_blockStep η θ B N
  measurable_output _ := measurable_snd.snd

theorem blockFinish_eq_actual {d : ℕ} (f : Model.Space d → ℝ) (η θ B : ℝ)
    {N : ℕ} (hN : 0 < N) (start output : Model.Space d) (g : ℕ → Model.Space d)
    (hg : ∀ k < N, g k = gradient f (epochQuery f η θ start k)) :
    blockFinish η θ B N (start, g, output) =
      (restartPoint f η θ B N start, fun _ => 0,
        if (N : ℝ) * epochEnergy f η θ start N ≤ B ^ 2 then epochOutput f η θ N start else output) := by
  unfold blockFinish
  simp only [replyRestartPoint_eq f η θ B N start g hg,
    replyEnergy_eq_epochEnergy f η θ start g N hg, replyOutput_eq f η θ hN start g hg]

end

end RandomizedFO2003.Accelerated
