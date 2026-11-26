import Matvec.MeasurableOracleAdapter

/-! Joint measurability of an ordinary policy in its seed and oracle input. -/
namespace Matvec.MeasurableSimulation.Policy
open Matrix MeasureTheory
open scoped Matrix

theorem joint_measurable_transcript {Q R O Seed X : Type*}
    [MeasurableSpace Q] [MeasurableSpace R] [MeasurableSpace O]
    [MeasurableSpace Seed] [MeasurableSpace X] {T : ℕ}
    (alg : Policy Q R O T Seed) (oracle : X → Q → R)
    (horacle : Measurable (fun p : X × Q => oracle p.1 p.2)) (j : ℕ) :
    Measurable (fun p : Seed × X => alg.transcript (oracle p.2) p.1 j) := by
  induction j with
  | zero => exact measurable_const
  | succ j ih =>
    have hq := (alg.query_measurable j).comp (measurable_fst.prodMk ih)
    have hr := horacle.comp (measurable_snd.prodMk hq)
    apply measurable_pi_lambda
    intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simpa only [transcript, Fin.snoc_last] using hr
    · simpa only [transcript, Fin.snoc_castSucc] using (measurable_pi_apply i).comp ih

theorem joint_measurable_run {Q R O Seed X : Type*}
    [MeasurableSpace Q] [MeasurableSpace R] [MeasurableSpace O]
    [MeasurableSpace Seed] [MeasurableSpace X] {T : ℕ}
    (alg : Policy Q R O T Seed) (oracle : X → Q → R)
    (horacle : Measurable (fun p : X × Q => oracle p.1 p.2)) :
    Measurable (fun p : Seed × X => alg.run (oracle p.2) p.1) :=
  alg.output_measurable.comp
    (measurable_fst.prodMk (alg.joint_measurable_transcript oracle horacle T))

theorem joint_measurable_ambient_run {m n T : ℕ} {O Seed : Type*}
    [MeasurableSpace O] [MeasurableSpace Seed]
    (alg : Policy (AmbientQuery m n) (AmbientQuery m n) O T Seed) :
    Measurable (fun p : Seed × Matrix (Fin m) (Fin n) ℝ =>
      alg.run (fun q => (p.2 *ᵥ q.2, p.2ᵀ *ᵥ q.1)) p.1) := by
  apply alg.joint_measurable_run
    (fun (A : Matrix (Fin m) (Fin n) ℝ) q => (A *ᵥ q.2, Aᵀ *ᵥ q.1))
  apply Measurable.prodMk <;> apply measurable_pi_lambda
  all_goals
    intro i
    simp only [Matrix.mulVec, Matrix.transpose_apply, dotProduct]
    fun_prop

end Matvec.MeasurableSimulation.Policy
