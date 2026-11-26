import FreshGradientMinimax.Algorithm

/-! Exact execution semantics and the unstopped first-disagreement argument.
Oracle maps here may depend on time, allowing a fixed realization of fresh coins.
No conditioning on earlier nonviolations is used in the pathwise theorem. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace Algorithm
variable {dx dy : ℕ} {Seed : Type*} [MeasurableSpace Seed] (A : Algorithm dx dy Seed)

def deterministicStep (q : Joint dx dy → Joint dx dy) (n : ℕ)
    (s : RunState dx dy Seed n) : RunState dx dy Seed (n + 1) :=
  A.append n (s, q (A.query n s))

theorem deterministicStep_measurable {q : Joint dx dy → Joint dx dy} (hq : Measurable q) (n : ℕ) :
    Measurable (A.deterministicStep q n) :=
  (A.append_measurable n).comp (measurable_id.prodMk (hq.comp (A.query_measurable n)))

def deterministicRun (A : Algorithm dx dy Seed) (q : ℕ → Joint dx dy → Joint dx dy) :
    (n : ℕ) → Seed → RunState dx dy Seed n
  | 0 => initial
  | n + 1 => fun seed => A.deterministicStep (q n) n (A.deterministicRun q n seed)

theorem deterministicRun_measurable (q : ℕ → Joint dx dy → Joint dx dy)
    (hq : ∀ n, Measurable (q n)) (n : ℕ) : Measurable (A.deterministicRun q n) := by
  induction n with
  | zero => exact initial_measurable
  | succ n ih => exact (A.deterministicStep_measurable (hq n) n).comp ih

theorem stepKernel_exact {q : Joint dx dy → Joint dx dy} (hq : Measurable q) (n : ℕ) :
    A.stepKernel (Kernel.deterministic q hq) n =
      Kernel.deterministic (A.deterministicStep q n) (A.deterministicStep_measurable hq n) := by
  ext s t ht
  rw [stepKernel, Kernel.map_apply' _ (A.append_measurable n) _ ht]
  rw [Kernel.prod_apply, Kernel.id_apply]
  change (Measure.dirac s).prod (Measure.dirac (q (A.query n s))) ((A.append n) ⁻¹' t) = _
  rw [Measure.dirac_prod_dirac, Measure.dirac_apply' _ ((A.append_measurable n) ht),
    Kernel.deterministic_apply' _ _ ht]
  rfl

theorem historyKernel_exact {q : Joint dx dy → Joint dx dy} (hq : Measurable q) (n : ℕ) :
    A.historyKernel (Kernel.deterministic q hq) n =
      Kernel.deterministic (A.deterministicRun (fun _ => q) n)
        (A.deterministicRun_measurable (fun _ => q) (fun _ => hq) n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [historyKernel, A.stepKernel_exact hq, ih, Kernel.deterministic_comp_deterministic]
    rfl

theorem outputLaw_exact (ν : Measure Seed) {q : Joint dx dy → Joint dx dy}
    (hq : Measurable q) (n : ℕ) :
    A.outputLaw ν (Kernel.deterministic q hq) n =
      ν.map (fun seed => A.output n (A.deterministicRun (fun _ => q) n seed)) := by
  unfold outputLaw outputKernel
  rw [A.historyKernel_exact hq, Kernel.deterministic_map _ (A.output_measurable n),
    Measure.deterministic_comp_eq_map]
  rfl

/-- Equality is checked at the auxiliary trajectory's queries, without stopping
that trajectory on earlier violations. This includes the private seed. -/
theorem first_exit_transcript_identity
    (qtrue qaux : ℕ → Joint dx dy → Joint dx dy) (seed : Seed) (N : ℕ)
    (hlocal : ∀ t < N,
      qtrue t (A.query t (A.deterministicRun qaux t seed)) =
        qaux t (A.query t (A.deterministicRun qaux t seed))) :
    ∀ t ≤ N, A.deterministicRun qtrue t seed = A.deterministicRun qaux t seed := by
  intro t ht
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [deterministicRun, deterministicStep]
    rw [ih (by omega), hlocal t (by omega)]

/-- The terminal output need not have been queried: it is any measurable map
of the complete transcript, so equality of transcripts gives equality of outputs. -/
theorem first_exit_output_identity
    (qtrue qaux : ℕ → Joint dx dy → Joint dx dy) (seed : Seed) (N : ℕ)
    (hlocal : ∀ t < N,
      qtrue t (A.query t (A.deterministicRun qaux t seed)) =
        qaux t (A.query t (A.deterministicRun qaux t seed))) :
    A.output N (A.deterministicRun qtrue N seed) =
      A.output N (A.deterministicRun qaux N seed) := by
  rw [A.first_exit_transcript_identity qtrue qaux seed N hlocal N le_rfl]

end Algorithm
end FreshGradientMinimax
