import SampleReuse.CurvatureFirstProgram

/-! The combined curvature-first controller is an observable-prefix measurable
reply-only algorithm, including its numerical stopping and Rayleigh decisions. -/

open MeasureTheory SecondOrder
open scoped Classical

namespace SampleReuse
noncomputable section

variable {S E : Type} [MeasurableSpace S] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [BorelSpace E] [SecondCountableTopology E] in
theorem measurable_natChoice (f : ℕ → S → E) (hf : ∀ n, Measurable (f n))
    (k : S → ℕ) (hk : Measurable k) : Measurable (fun s => f (k s) s) := by
  have hm : Measurable (fun w : S × ℕ => f w.2 w.1) := measurable_from_prod_countable hf
  exact hm.comp (measurable_id.prodMk hk)

theorem checkpointProgram_measurableFamily {H d B : ℕ} (hB : 0 < B) (scale σ L : ℝ)
    (q₀ : PersistentQuery H d) (flag : Bool) (project : PersistentReply d → E) (hp : Measurable project)
    (reserve : ℕ → Fin B → Fin H) (k : S → ℕ) (hk : Measurable k)
    (cache : S → TreeCache d E) (hc : Measurable cache) (x : S → Point d) (hx : Measurable x) :
    OracleProgram.MeasurableFamily q₀ 0
      (fun s => checkpointProgram hB scale σ L flag project reserve (k s) (cache s) (x s)) := by
  apply OracleProgram.MeasurableFamily.chooseNat
    (fun j s => checkpointProgram hB scale σ L flag project reserve j (cache s) (x s)) _ k hk
  intro j
  unfold checkpointProgram
  by_cases hj : j = 0
  · simp only [if_pos hj]
    exact (fieldRootProgram_measurableFamily q₀ flag project hp).comp
      (fun s => (reserve j, x s)) (measurable_const.prodMk hx)
  · simp only [if_neg hj]
    have hpoint : Measurable (fun s => (cache s (ancestorParent j)).1) :=
      ((measurable_pi_apply _).comp hc).fst
    have hfixed (n : ℕ) : OracleProgram.MeasurableFamily q₀ 0
        (fun s => fieldChordProgram flag project (fun i => reserve j (prefixHandles hB n i))
          (x s) (cache s (ancestorParent j)).1) :=
      (fieldChordProgram_measurableFamily q₀ flag project hp).comp
        (fun s => ((fun i => reserve j (prefixHandles hB n i)), x s, (cache s (ancestorParent j)).1))
        (measurable_const.prodMk (hx.prodMk hpoint))
    have hb : Measurable (fun s => checkpointBatchSize (B := B) scale σ L j (cache s) (x s)) := by
      simpa only [checkpointBatchSize, if_neg hj] using
        chordBatchSize_measurable scale σ L x (fun s => (cache s (ancestorParent j)).1) hx hpoint
    exact OracleProgram.MeasurableFamily.chooseNat _ hfixed _ hb

omit [NormedSpace ℝ E] in
theorem checkpointValue_measurable {d : ℕ} (k : S → ℕ) (hk : Measurable k)
    (cache : S → TreeCache d E) (hc : Measurable cache) (packet : S → E) (hp : Measurable packet) :
    Measurable (fun s => checkpointValue (k s) (cache s) (packet s)) := by
  apply measurable_natChoice (fun j s => checkpointValue j (cache s) (packet s)) _ k hk
  intro j
  dsimp only [checkpointValue]
  split_ifs
  · exact hp
  · exact (((measurable_pi_apply _).comp hc).snd).add hp

omit [NormedSpace ℝ E] in
theorem installCheckpoint_measurable {d : ℕ} (k : S → ℕ) (hk : Measurable k)
    (cache : S → TreeCache d E) (hc : Measurable cache) (x : S → Point d) (hx : Measurable x)
    (packet : S → E) (hp : Measurable packet) :
    Measurable (fun s => installCheckpoint (k s) (cache s) (x s) (packet s)) := by
  classical
  apply measurable_pi_lambda
  intro j
  have hm := hx.prodMk (checkpointValue_measurable k hk cache hc packet hp)
  have hold := (measurable_pi_apply j).comp hc
  have he : MeasurableSet {s | j = k s} := measurableSet_eq_fun_of_countable measurable_const hk
  have hi : Measurable (fun s => if j = k s then
      (x s, checkpointValue (k s) (cache s) (packet s)) else cache s j) :=
    Measurable.ite he hm hold
  simpa only [installCheckpoint, Function.update_apply, checkpointValue] using hi

theorem gradientMove_measurable {d : ℕ} (P : Parameters) (ε : ℝ) :
    Measurable (fun w : Point d × Point d => gradientMove P ε w.1 w.2) := by
  unfold gradientMove
  have hg : Measurable (fun w : Point d × Point d => (‖w.2‖⁻¹ : ℝ) • w.2) :=
    measurable_snd.norm.inv.smul measurable_snd
  exact measurable_fst.add (hg.const_smul (-(ε / (4 * P.gradientLip))))

theorem curvatureNext_measurable {d : ℕ} (a : ℝ) :
    Measurable (fun w : Point d × (Point d × Bool) => curvatureNext a w.1 w.2.1 w.2.2) := by
  unfold curvatureNext
  exact measurable_fst.add
    (((measurable_of_countable signValue).comp measurable_snd.snd).mul_const a |>.smul measurable_snd.fst)

end
end SampleReuse
