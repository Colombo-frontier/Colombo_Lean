import SampleReuse.OracleDerivativeCaps

open SecondOrder MeasureTheory

namespace SampleReuse.OracleDerivativeCaps

variable {Q Y O : Type}

theorem view_cap_zero (flag : Q → Bool) (abort : O) (q₀ : Q) (o₀ : O)
    (g h : ℕ) (p : OracleProgram Q Y O) (ys : ℕ → Y) :
    OracleProgram.view q₀ o₀ (OracleProgram.readAnswers (cap flag abort g h p) ys 0) =
      if OracleProgram.finished p then OracleProgram.view q₀ o₀ p else
      if flag (OracleProgram.query q₀ p) then
        if g=0 then (q₀,abort,true) else (OracleProgram.query q₀ p,o₀,false)
      else if h=0 then (q₀,abort,true) else (OracleProgram.query q₀ p,o₀,false) := by
  cases p with
  | done o => rfl
  | request q k =>
    by_cases hf : flag q = true
    · by_cases hg : g=0 <;>
        simp [cap,hf,hg,OracleProgram.readAnswers,OracleProgram.view,
          OracleProgram.finished,OracleProgram.query,OracleProgram.output]
    · by_cases hh : h=0 <;>
        simp [cap,hf,hh,OracleProgram.readAnswers,OracleProgram.view,
          OracleProgram.finished,OracleProgram.query,OracleProgram.output]

theorem view_cap_succ (flag : Q → Bool) (abort : O) (q₀ : Q) (o₀ : O)
    (g h : ℕ) (p : OracleProgram Q Y O) (ys : ℕ → Y) (n : ℕ) :
    OracleProgram.view q₀ o₀ (OracleProgram.readAnswers (cap flag abort g h p) ys (n+1)) =
      if OracleProgram.finished p then OracleProgram.view q₀ o₀ p else
      if flag (OracleProgram.query q₀ p) then
        if g=0 then (q₀,abort,true) else OracleProgram.view q₀ o₀
          (OracleProgram.readAnswers (cap flag abort (g-1) h (OracleProgram.advance p (ys 0)))
            (fun i => ys (i+1)) n)
      else if h=0 then (q₀,abort,true) else OracleProgram.view q₀ o₀
          (OracleProgram.readAnswers (cap flag abort g (h-1) (OracleProgram.advance p (ys 0)))
            (fun i => ys (i+1)) n) := by
  cases p with
  | done o => simp [cap,OracleProgram.readAnswers_done,OracleProgram.finished]
  | request q k =>
    by_cases hf : flag q = true
    · by_cases hg : g=0 <;>
        simp [cap,hf,hg,OracleProgram.readAnswers_done,OracleProgram.readAnswers_request,
          OracleProgram.view,OracleProgram.finished,OracleProgram.query,OracleProgram.output,
          OracleProgram.advance]
    · by_cases hh : h=0 <;>
        simp [cap,hf,hh,OracleProgram.readAnswers_done,OracleProgram.readAnswers_request,
          OracleProgram.view,OracleProgram.finished,OracleProgram.query,OracleProgram.output,
          OracleProgram.advance]

variable {Ξ : Type} [MeasurableSpace Ξ] [MeasurableSpace Q]
  [MeasurableSpace Y] [MeasurableSpace O]

/-- Capping is an observable-prefix measurable transformation. It inspects
only the next requested derivative and the two integer counters. -/
theorem cap_measurableFamily (flag : Q → Bool) (hflag : Measurable flag) (abort : O)
    {q₀ : Q} {o₀ : O} {p : Ξ → OracleProgram Q Y O}
    (hp : OracleProgram.MeasurableFamily q₀ o₀ p) (g h : ℕ) :
    OracleProgram.MeasurableFamily q₀ o₀ (fun ξ => cap flag abort g h (p ξ)) := by
  apply OracleProgram.measurableFamily_of_view
  intro n
  induction n generalizing Ξ g h with
  | zero =>
    have he : MeasurableSet {w : Ξ × (ℕ → Y) | OracleProgram.finished (p w.1)=true} :=
      (hp.finished 0) (measurableSet_singleton true)
    have hf : MeasurableSet {w : Ξ × (ℕ → Y) | flag (OracleProgram.query q₀ (p w.1))=true} :=
      (hflag.comp (hp.query 0)) (measurableSet_singleton true)
    have hrequest : Measurable (fun w : Ξ × (ℕ → Y) => (OracleProgram.query q₀ (p w.1),o₀,false)) :=
      (hp.query 0).prodMk (measurable_const.prodMk measurable_const)
    have hG : Measurable (fun w : Ξ × (ℕ → Y) =>
        if g=0 then (q₀,abort,true) else (OracleProgram.query q₀ (p w.1),o₀,false)) := by
      split_ifs
      · exact measurable_const
      · exact hrequest
    have hH : Measurable (fun w : Ξ × (ℕ → Y) =>
        if h=0 then (q₀,abort,true) else (OracleProgram.query q₀ (p w.1),o₀,false)) := by
      split_ifs
      · exact measurable_const
      · exact hrequest
    simp_rw [view_cap_zero]
    exact Measurable.ite he (hp.view 0) (Measurable.ite hf hG hH)
  | succ n ih =>
    have he : MeasurableSet {w : Ξ × (ℕ → Y) | OracleProgram.finished (p w.1)=true} :=
      (hp.finished 0) (measurableSet_singleton true)
    have hf : MeasurableSet {w : Ξ × (ℕ → Y) | flag (OracleProgram.query q₀ (p w.1))=true} :=
      (hflag.comp (hp.query 0)) (measurableSet_singleton true)
    have ht : Measurable (fun w : Ξ × (ℕ → Y) => ((w.1,w.2 0),fun i => w.2 (i+1))) :=
      (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd)).prodMk
        (measurable_pi_lambda _ (fun i => (measurable_pi_apply (i+1)).comp measurable_snd))
    have hGnext := (ih (p := fun w : Ξ × Y => OracleProgram.advance (p w.1) w.2)
      hp.advance (g-1) h).comp ht
    have hHnext := (ih (p := fun w : Ξ × Y => OracleProgram.advance (p w.1) w.2)
      hp.advance g (h-1)).comp ht
    have hG : Measurable (fun w : Ξ × (ℕ → Y) => if g=0 then (q₀,abort,true) else
        OracleProgram.view q₀ o₀ (OracleProgram.readAnswers
          (cap flag abort (g-1) h (OracleProgram.advance (p w.1) (w.2 0)))
          (fun i => w.2 (i+1)) n)) := by
      split_ifs
      · exact measurable_const
      · exact hGnext
    have hH : Measurable (fun w : Ξ × (ℕ → Y) => if h=0 then (q₀,abort,true) else
        OracleProgram.view q₀ o₀ (OracleProgram.readAnswers
          (cap flag abort g (h-1) (OracleProgram.advance (p w.1) (w.2 0)))
          (fun i => w.2 (i+1)) n)) := by
      split_ifs
      · exact measurable_const
      · exact hHnext
    simp_rw [view_cap_succ]
    exact Measurable.ite he (hp.view 0) (Measurable.ite hf hG hH)

end SampleReuse.OracleDerivativeCaps
