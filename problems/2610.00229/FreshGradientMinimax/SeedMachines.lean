import FreshGradientMinimax.IndependentMachines
import FreshGradientMinimax.FiniteMixture

/-! A discrete label is drawn in the initial seed and retained during
all original queries. Each branch may have its own finite horizon. The
stopped kernel reads an actual transcript of precisely that length. -/

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

def indexedKernel (L : ℕ → Kernel X Y) : Kernel (X × ℕ) Y where
  toFun s := L s.2 s.1
  measurable' := measurable_from_prod_countable (fun j => (L j).measurable)

instance indexedKernel_markov (L : ℕ → Kernel X Y) [∀ j, IsMarkovKernel (L j)] :
    IsMarkovKernel (indexedKernel L) := ⟨fun s => inferInstanceAs (IsProbabilityMeasure (L s.2 s.1))⟩

def finiteLabelKernel (p : ℕ → ℝ) (k : ℕ) : Kernel X (X × ℕ) :=
  finiteMixtureKernel p (fun j => Kernel.deterministic (fun q : X => (q, j))
    (measurable_id.prodMk measurable_const)) k

theorem finiteLabelKernel_markov (p : ℕ → ℝ) (k : ℕ) (hp : ∀ j < k, 0 ≤ p j)
    (hs : ∑ j ∈ Finset.range k, p j = 1) : IsMarkovKernel (finiteLabelKernel (X := X) p k) :=
  finiteMixtureKernel_markov _ _ _ hp hs

theorem finiteMixtureKernel_comp {Z : Type*} [MeasurableSpace Z]
    (p : ℕ → ℝ) (L : ℕ → Kernel X Y) (k : ℕ) (R : Kernel Y Z) :
    R ∘ₖ finiteMixtureKernel p L k = finiteMixtureKernel p (fun j => R ∘ₖ L j) k := by
  apply Kernel.ext
  intro q
  apply Measure.ext
  intro A hA
  simp only [Kernel.comp_apply' _ _ _ hA, finiteMixtureKernel_apply, lintegral_finset_sum_measure,
    lintegral_smul_measure, Measure.finset_sum_apply, Measure.smul_apply, smul_eq_mul]

namespace OracleMachine
variable {dx dy : ℕ} {State Seed Out : Type*}
variable [MeasurableSpace State] [MeasurableSpace Seed] [MeasurableSpace Out]

def select (M : ℕ → OracleMachine dx dy State) : OracleMachine dx dy (State × ℕ) where
  query n s := (M s.2).query n s.1
  update n z := ((M z.1.2).update n (z.1.1, z.2), z.1.2)
  output n s := (M s.2).output n s.1
  query_measurable n := measurable_from_prod_countable (fun j => (M j).query_measurable n)
  update_measurable n := by
    have hh : Measurable (fun z : (State × Joint dx dy) × ℕ => (M z.2).update n z.1) :=
      measurable_from_prod_countable (fun j => (M j).update_measurable n)
    exact (hh.comp ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd)).prodMk measurable_fst.snd
  output_measurable n := measurable_from_prod_countable (fun j => (M j).output_measurable n)

theorem select_run_fixed (M : ℕ → OracleMachine dx dy State) (j : ℕ)
    (init : Seed → State) (hinit : Measurable init)
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (n : ℕ) :
    (select M).runKernel (fun q => (init q, j)) (hinit.prodMk measurable_const) K n =
      ((M j).runKernel init hinit K n).map (fun s => (s, j)) :=
  (M j).runKernel_transport (select M) (fun s => (s, j)) (measurable_id.prodMk measurable_const)
    init hinit K (fun i => (M j).stepKernel_transport (select M) _ _ K i
      (fun _ => rfl) (fun _ _ => rfl)) n

def selectInitial (init : ℕ → Seed → State) (s : Seed × ℕ) : State × ℕ := (init s.2 s.1, s.2)

theorem selectInitial_measurable (init : ℕ → Seed → State) (hinit : ∀ j, Measurable (init j)) :
    Measurable (selectInitial init) :=
  (measurable_from_prod_countable hinit).prodMk measurable_snd

theorem select_run_apply (M : ℕ → OracleMachine dx dy State) (init : ℕ → Seed → State)
    (hinit : ∀ j, Measurable (init j)) (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K]
    (n : ℕ) (q : Seed) (j : ℕ) :
    (select M).runKernel (selectInitial init) (selectInitial_measurable init hinit) K n (q, j) =
      ((M j).runKernel (init j) (hinit j) K n q).map (fun s => (s, j)) := by
  have h := congrArg (fun L : Kernel Seed (State × ℕ) => L q) (select_run_fixed M j (init j) (hinit j) K n)
  dsimp only at h
  rw [runKernel_apply, Kernel.map_apply (f := fun s : State => (s, j)) _
    (measurable_id.prodMk measurable_const)] at h
  rw [runKernel_apply]
  exact h

def seedStoppedKernel (M : OracleMachine dx dy State) (init : Seed → State) (hinit : Measurable init)
    (K : Kernel (Joint dx dy) (Joint dx dy)) (T : Seed → ℕ) (hT : Measurable T)
    (read : State → Out) : Kernel Seed (Out × ℕ) :=
  (indexedKernel (fun n => ((M.compile init hinit).historyKernel K n).map
    (fun h => (read (M.replay init n h), n)))).comap (fun q => (q, T q)) (measurable_id.prodMk hT)

theorem seedStoppedKernel_apply (M : OracleMachine dx dy State) (init : Seed → State) (hinit : Measurable init)
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (T : Seed → ℕ) (hT : Measurable T)
    (read : State → Out) (hread : Measurable read) (q : Seed) :
    M.seedStoppedKernel init hinit K T hT read q =
      (M.runKernel init hinit K (T q) q).map (fun s => (read s, T q)) := by
  rw [seedStoppedKernel, Kernel.comap_apply]
  change (((M.compile init hinit).historyKernel K (T q)).map
    (fun h => (read (M.replay init (T q) h), T q))) q = _
  rw [M.runKernel_eq_history, Kernel.map_apply _ (M.replay_measurable init hinit (T q)),
    Measure.map_map (f := M.replay init (T q)) (g := fun s => (read s, T q))
      (hread.prodMk measurable_const) (M.replay_measurable init hinit (T q)),
    Kernel.map_apply (f := fun h => (read (M.replay init (T q) h), T q)) _
      ((hread.comp (M.replay_measurable init hinit (T q))).prodMk measurable_const)]
  rfl

theorem seedStoppedKernel_markov (M : OracleMachine dx dy State) (init : Seed → State) (hinit : Measurable init)
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (T : Seed → ℕ) (hT : Measurable T)
    (read : State → Out) (hread : Measurable read) : IsMarkovKernel (M.seedStoppedKernel init hinit K T hT read) := by
  constructor
  intro q
  rw [M.seedStoppedKernel_apply init hinit K T hT read hread q]
  exact isProbabilityMeasure_map (hread.prodMk measurable_const).aemeasurable

def selectRead (read : ℕ → State → Out) (s : State × ℕ) : Out := read s.2 s.1

theorem selectRead_measurable (read : ℕ → State → Out) (hread : ∀ j, Measurable (read j)) :
    Measurable (selectRead read) := measurable_from_prod_countable hread

theorem select_stopped_apply (M : ℕ → OracleMachine dx dy State) (init : ℕ → Seed → State)
    (hinit : ∀ j, Measurable (init j)) (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K]
    (T : ℕ → ℕ) (read : ℕ → State → Out) (hread : ∀ j, Measurable (read j)) (q : Seed) (j : ℕ) :
    (select M).seedStoppedKernel (selectInitial init) (selectInitial_measurable init hinit) K
      (fun s => T s.2) ((measurable_of_countable T).comp measurable_snd) (selectRead read) (q, j) =
      ((M j).runKernel (init j) (hinit j) K (T j) q).map (fun s => (read j s, T j)) := by
  rw [seedStoppedKernel_apply _ _ _ _ _ _ _ (selectRead_measurable read hread), select_run_apply,
    Measure.map_map (f := fun s : State => (s, j))
      (g := fun s : State × ℕ => (selectRead read s, T j))
      ((selectRead_measurable read hread).prodMk measurable_const) (measurable_id.prodMk measurable_const)]
  rfl

theorem select_stopped_seed_law (M : ℕ → OracleMachine dx dy State) (init : ℕ → Seed → State)
    (hinit : ∀ j, Measurable (init j)) (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K]
    (T : ℕ → ℕ) (read : ℕ → State → Out) (hread : ∀ j, Measurable (read j)) (p : ℕ → ℝ) (k : ℕ) :
    (select M).seedStoppedKernel (selectInitial init) (selectInitial_measurable init hinit) K
      (fun s => T s.2) ((measurable_of_countable T).comp measurable_snd) (selectRead read) ∘ₖ
        finiteLabelKernel p k =
    finiteMixtureKernel p (fun j => ((M j).runKernel (init j) (hinit j) K (T j)).map
      (fun s => (read j s, T j))) k := by
  rw [finiteLabelKernel, finiteMixtureKernel_comp]
  congr 1
  funext j
  apply Kernel.ext
  intro q
  rw [Kernel.comp_deterministic_eq_comap, Kernel.comap_apply, select_stopped_apply M init hinit K T read hread q j,
    Kernel.map_apply (f := fun s => (read j s, T j)) _ ((hread j).prodMk measurable_const)]

end OracleMachine
end FreshGradientMinimax
