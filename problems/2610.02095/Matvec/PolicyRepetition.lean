import Matvec.PolicyComposition

/-! Finite copies of any measurable oracle policy, with the exact sum budget
and a pathwise vector of outputs. Independence is supplied by the product
measure on the exposed seed tuple, separately from the execution semantics. -/

namespace Matvec.MeasurableSimulation.Policy
open MeasureTheory

variable {Q R O Seed : Type*} [MeasurableSpace Q] [MeasurableSpace R]
  [MeasurableSpace O] [MeasurableSpace Seed] {T : ℕ}

def collect (q₀ : Q) (alg : Policy Q R O T Seed) :
    (L : ℕ) → Policy Q R (Fin L → O) (L * T) (Fin L → Seed)
  | 0 => (pure q₀ (fun _ => Fin.elim0) measurable_const).castHorizon (by omega)
  | L + 1 =>
      ((alg.seedMap (fun seeds : Fin (L + 1) → Seed => seeds 0) (measurable_pi_apply 0)).bind
        (((collect q₀ alg L).seedMap
          (fun p : (Fin (L + 1) → Seed) × O => fun i => p.1 i.succ) (by fun_prop)).mapOutput
          (fun p out => Fin.cons p.2 out) (by
            apply measurable_pi_lambda
            intro i
            refine Fin.cases ?_ (fun i => ?_) i
            · exact measurable_snd.comp measurable_fst
            · exact (measurable_pi_apply i).comp measurable_snd))).castHorizon (by ring)

theorem collect_run (q₀ : Q) (alg : Policy Q R O T Seed) (oracle : Q → R)
    (L : ℕ) (seeds : Fin L → Seed) :
    (collect q₀ alg L).run oracle seeds = fun i => alg.run oracle (seeds i) := by
  induction L with
  | zero => exact Subsingleton.elim _ _
  | succ L ih =>
    simp only [collect, castHorizon_run, bind_run, seedMap_run, mapOutput_run, ih]
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> rfl

end Matvec.MeasurableSimulation.Policy
