import SecondOrder.ExactOracleProgram
import SecondOrder.DrawsLawTransport

open MeasureTheory

namespace SecondOrder
namespace OracleProgram
noncomputable section

variable {Q Y O O' Ω Ξ : Type}

def runDraws (q₀ : Q) (reply : Q → Ω → Y) (p : OracleProgram Q Y O) :
    (n : ℕ) → Draws Ω n → OracleProgram Q Y O
  | 0, _ => p
  | n+1, w =>
    let s := runDraws q₀ reply p n w.1
    advance s (reply (query q₀ s) w.2)

theorem run_eq_runDraws (q₀ : Q) (reply : Q → Ω → Y) (zs : ℕ → Ω)
    (p : OracleProgram Q Y O) (n : ℕ) (w : Draws Ω n)
    (hz : ∀ i : Fin n, zs i=drawsVector id n w i) :
    run q₀ reply zs p n=runDraws q₀ reply p n w := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hpre : ∀ i : Fin n, zs i=drawsVector id n w.1 i := by
      intro i
      simpa only [drawsVector,Fin.snoc_castSucc] using hz i.castSucc
    have hlast : zs n=w.2 := by
      simpa only [drawsVector,Fin.snoc_last,Fin.val_last,id_eq] using hz (Fin.last n)
    simp only [run,runDraws,ih w.1 hpre,hlast]

theorem runDraws_append (q₀ : Q) (reply : Q → Ω → Y) (p : OracleProgram Q Y O)
    (n m : ℕ) (u : Draws Ω n) (v : Draws Ω m) :
    runDraws q₀ reply p (n+m) (drawsAppend n m u v)=
      runDraws q₀ reply (runDraws q₀ reply p n u) m v := by
  induction m with
  | zero => rfl
  | succ m ih =>
    exact congrArg (fun s : OracleProgram Q Y O => advance s (reply (query q₀ s) v.2)) (ih v.1)

theorem runDraws_bind_prefix (q₀ : Q) (reply : Q → Ω → Y) (a₀ : Ω)
    {p : OracleProgram Q Y O} {N : ℕ} (hp : UsesExactly N p)
    (f : O → OracleProgram Q Y O') (n : ℕ) (hn : n≤N) (w : Draws Ω n) :
    runDraws q₀ reply (bind p f) n w=bind (runDraws q₀ reply p n w) f := by
  let zs := finiteHistoryTape a₀ n (drawsHistory n w)
  have hz : ∀ i : Fin n, zs i=drawsVector id n w i := by
    intro i
    exact (finiteHistoryTape_historyDraws a₀ n (drawsHistory n w) i).trans
      (congrArg (fun u => drawsVector id n u i) (historyDraws_drawsHistory n w))
  rw [←run_eq_runDraws q₀ reply zs (bind p f) n w hz,
    run_bind_prefix q₀ reply zs hp f n hn,run_eq_runDraws q₀ reply zs p n w hz]

theorem runDraws_done (q₀ : Q) (reply : Q → Ω → Y) (a₀ : Ω)
    {p : OracleProgram Q Y O} {N : ℕ} (hp : UsesAtMost N p) (w : Draws Ω N) :
    ∃ o, runDraws q₀ reply p N w=.done o := by
  let zs := finiteHistoryTape a₀ N (drawsHistory N w)
  have hz : ∀ i : Fin N, zs i=drawsVector id N w i := by
    intro i
    exact (finiteHistoryTape_historyDraws a₀ N (drawsHistory N w) i).trans
      (congrArg (fun u => drawsVector id N u i) (historyDraws_drawsHistory N w))
  rw [←run_eq_runDraws q₀ reply zs p N w hz]
  exact run_done q₀ reply zs hp

theorem runDraws_bind_of_exact (q₀ : Q) (reply : Q → Ω → Y) (a₀ : Ω)
    {p : OracleProgram Q Y O} {N : ℕ} (hp : UsesExactly N p)
    (f : O → OracleProgram Q Y O') (u : Draws Ω N) {o : O}
    (ho : runDraws q₀ reply p N u=.done o) (M : ℕ) (v : Draws Ω M) :
    runDraws q₀ reply (bind p f) (N+M) (drawsAppend N M u v)=
      runDraws q₀ reply (f o) M v := by
  rw [runDraws_append,runDraws_bind_prefix q₀ reply a₀ hp f N le_rfl,ho,bind_done]

theorem algorithm_history_output (q₀ : Q) (y₀ : Y) (o₀ : O) (p : OracleProgram Q Y O)
    (reply : Q → Ω → Y) (a₀ : Ω) (n : ℕ) (h : FiniteHistory Unit Ω n) :
    oracleHistoryOutput (algorithm q₀ y₀ o₀ p) reply n h=
      output o₀ (runDraws q₀ reply p n (historyDraws n h)) := by
  rw [oracleHistoryOutput_tape _ reply a₀,algorithm_output,
    run_eq_runDraws q₀ reply _ p n (historyDraws n h)
      (finiteHistoryTape_historyDraws a₀ n h)]

variable [MeasurableSpace Q] [MeasurableSpace Y] [MeasurableSpace O]
  [MeasurableSpace O'] [MeasurableSpace Ω] [MeasurableSpace Ξ]

theorem MeasurableFamily.runDrawsOutput {q₀ : Q} {o₀ : O} {p : Ξ → OracleProgram Q Y O}
    (hp : MeasurableFamily q₀ o₀ p) (y₀ : Y) (a₀ : Ω)
    (reply : Q → Ω → Y) (hr : Measurable (fun w : Q × Ω => reply w.1 w.2)) (n : ℕ) :
    Measurable (fun w : Ξ × Draws Ω n => OracleProgram.output o₀ (runDraws q₀ reply (p w.1) n w.2)) := by
  have hm := oracleHistoryOutput_measurable (fun ξ => algorithm q₀ y₀ o₀ (p ξ))
    (algorithm_measurable y₀ hp) reply hr n
  have ht : Measurable (fun w : Ξ × Draws Ω n => (w.1,drawsHistory n w.2)) :=
    measurable_fst.prodMk ((drawsHistory_measurable n).comp measurable_snd)
  have hh := hm.comp ht
  simpa only [Function.comp_def,algorithm_history_output q₀ y₀ o₀ _ reply a₀,
    historyDraws_drawsHistory] using hh

def outputLaw (μ : Measure Ω) (q₀ : Q) (o₀ : O) (reply : Q → Ω → Y)
    (p : OracleProgram Q Y O) (n : ℕ) : Measure O :=
  Measure.map (fun w => output o₀ (runDraws q₀ reply p n w)) (drawsLaw μ n)

/-- The distribution used by the uniform oracle interface is exactly the
reply-program distribution. The unused tape extension does not affect it. -/
theorem algorithm_history_outputLaw (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q₀ : Q) (y₀ : Y) (o₀ : O) (p : OracleProgram Q Y O)
    (hp : MeasurableFamily q₀ o₀ (fun _ : Unit => p)) (a₀ : Ω)
    (reply : Q → Ω → Y) (hr : Measurable (fun w : Q × Ω => reply w.1 w.2)) (n : ℕ) :
    Measure.map (oracleHistoryOutput (algorithm q₀ y₀ o₀ p) reply n) (oracleHistoryLaw μ n)=
      outputLaw μ q₀ o₀ reply p n := by
  have ht : Measurable (fun w : Draws Ω n => ((),w)) := measurable_const.prodMk measurable_id
  have hm := (hp.runDrawsOutput y₀ a₀ reply hr n).comp ht
  change Measurable (fun w : Draws Ω n => output o₀ (runDraws q₀ reply p n w)) at hm
  unfold outputLaw
  rw [←(historyDraws_measurePreserving μ n).map_eq,Measure.map_map hm (historyDraws_measurable n)]
  congr 1
  funext h
  exact algorithm_history_output q₀ y₀ o₀ p reply a₀ n h

end
end OracleProgram
end SecondOrder
