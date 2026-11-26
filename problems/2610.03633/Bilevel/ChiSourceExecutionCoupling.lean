import Bilevel.ChiHierarchyExecution
import Bilevel.BorelAdaptiveCoupling

/-! The finite-prefix source compiler is coupled to the original full SFO
execution by exact local reply identities along its own actual run. Halting
is respected, and equality is for the original state/output, not merely
for projection observations. -/
noncomputable section
namespace Bilevel.ChiHierarchyExecution
open ChiHierarchyIndex BorelAdaptive

variable {E S Q O Y : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
  [MeasurableSpace S] [MeasurableSpace Q] [MeasurableSpace O] [MeasurableSpace Y]

theorem original_run_eq_of_local (counts : ℕ → ℕ) (J : ℕ) (A : Program S Q O Y)
    (original : FiniteColumns counts J E → Q → Bool → O)
    (evaluate : Q → Store counts J E → Store counts J E → Bool → O)
    (U : FiniteColumns counts J E) (s : S) (draws : ℕ → Bool) (N : ℕ)
    (hlocal : ∀ t<N,
      let z := run counts J A evaluate U s draws t
      A.halt z.1=false → original U (A.query z.1) (draws t)=
        (response counts J evaluate U (A.query z.1,z.2) (draws t)).1) :
    BorelAdaptive.run A original U draws s N=(run counts J A evaluate U s draws N).1 := by
  induction N with
  | zero => rfl
  | succ N ih =>
    have hp : ∀ t<N,
        let z := run counts J A evaluate U s draws t
        A.halt z.1=false → original U (A.query z.1) (draws t)=
          (response counts J evaluate U (A.query z.1,z.2) (draws t)).1 :=
      fun t ht => hlocal t (by omega)
    rw [BorelAdaptive.run,ih hp]
    change BorelAdaptive.step A original U (draws N) (run counts J A evaluate U s draws N).1 =
      (BorelAdaptive.step (instrument counts J A) (response counts J evaluate) U (draws N)
        (run counts J A evaluate U s draws N)).1
    by_cases hh : A.halt (run counts J A evaluate U s draws N).1=true
    · simp only [BorelAdaptive.step,instrument,hh,if_true]
    · have hf := Bool.eq_false_of_not_eq_true hh
      have he := hlocal N (by omega) hf
      simp only [BorelAdaptive.step,instrument,hf,Bool.false_eq_true,if_false,he]

theorem original_output_eq_of_local (counts : ℕ → ℕ) (J : ℕ) (A : Program S Q O Y)
    (original : FiniteColumns counts J E → Q → Bool → O)
    (evaluate : Q → Store counts J E → Store counts J E → Bool → O)
    (U : FiniteColumns counts J E) (s : S) (draws : ℕ → Bool) (N : ℕ)
    (hlocal : ∀ t<N,
      let z := run counts J A evaluate U s draws t
      A.halt z.1=false → original U (A.query z.1) (draws t)=
        (response counts J evaluate U (A.query z.1,z.2) (draws t)).1) :
    A.output (BorelAdaptive.run A original U draws s N)=A.output (run counts J A evaluate U s draws N).1 :=
  congrArg A.output (original_run_eq_of_local counts J A original evaluate U s draws N hlocal)

end Bilevel.ChiHierarchyExecution
