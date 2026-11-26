import NCConcave16991.OracleProgram

/-! # Joint parameter measurability of actual finite oracle-program evaluation -/

noncomputable section

namespace NCConcave16991.OracleProgram

open MeasureTheory

set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true

variable {Q R X Ω Θ : Type*} [MeasurableSpace Q] [MeasurableSpace R]
  [MeasurableSpace X] [MeasurableSpace Ω] [MeasurableSpace Θ] {N : ℕ}

theorem fin_snoc_measurable (t : ℕ) :
    Measurable (fun p : (Fin t → R) × R ↦ Fin.snoc (α := fun _ : Fin (t + 1) ↦ R) p.1 p.2) := by
  apply measurable_pi_iff.mpr
  intro i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simpa only [Fin.snoc_last] using (measurable_snd : Measurable (fun p : (Fin t → R) × R ↦ p.2))
  · simpa only [Fin.snoc_castSucc,Function.comp_def] using ((measurable_pi_apply j).comp measurable_fst :
      Measurable (fun p : (Fin t → R) × R ↦ p.1 j))

theorem evalFrom_joint_measurable (P : Fixed Q R X Ω N) (A : Θ → Q → R)
    (hA : Measurable (Function.uncurry A)) (k t : ℕ) (ht : t + k = N) :
    Measurable (fun a : Θ × (Ω × (Fin t → R)) ↦ evalFrom P (A a.1) a.2.1 k t ht a.2.2) := by
  induction k generalizing t with
  | zero =>
      have hm : Measurable (fun a : Θ × (Ω × (Fin t → R)) ↦
          P.finish a.2.1 (fun i : Fin N ↦ a.2.2 (Fin.cast ht.symm i))) :=
        P.finish_measurable.comp ((measurable_fst.comp measurable_snd).prodMk
          (measurable_pi_iff.mpr (fun i ↦ (measurable_pi_apply (Fin.cast ht.symm i)).comp
            (measurable_snd.comp measurable_snd))))
      exact hm
  | succ k ih =>
      have hlt : t < N := by omega
      have hq : Measurable (fun a : Θ × (Ω × (Fin t → R)) ↦ P.ask ⟨t,hlt⟩ a.2.1 a.2.2) :=
        (P.ask_measurable ⟨t,hlt⟩).comp measurable_snd
      have hr : Measurable (fun a : Θ × (Ω × (Fin t → R)) ↦
          A a.1 (P.ask ⟨t,hlt⟩ a.2.1 a.2.2)) := hA.comp (measurable_fst.prodMk hq)
      have hs : Measurable (fun a : Θ × (Ω × (Fin t → R)) ↦
          Fin.snoc (α := fun _ : Fin (t + 1) ↦ R) a.2.2 (A a.1 (P.ask ⟨t,hlt⟩ a.2.1 a.2.2))) :=
        (fin_snoc_measurable t).comp ((measurable_snd.comp measurable_snd).prodMk hr)
      have hm := (ih (t + 1) (by omega)).comp
        (measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk hs))
      convert hm using 1
      funext a
      rfl

theorem eval_joint_measurable (P : Fixed Q R X Ω N) (A : Θ → Q → R)
    (hA : Measurable (Function.uncurry A)) :
    Measurable (fun a : Θ × Ω ↦ eval P (A a.1) a.2) := by
  have hm := (evalFrom_joint_measurable P A hA N 0 (by omega)).comp
    (measurable_fst.prodMk (measurable_snd.prodMk (measurable_const :
      Measurable (fun _ : Θ × Ω ↦ (Fin.elim0 : Fin 0 → R)))))
  exact hm

end NCConcave16991.OracleProgram
