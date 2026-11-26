import FreshGradientMinimax.ProgramComposition

/-! Zero-call maps, output transformations and finite program iteration. -/

set_option autoImplicit false
set_option maxHeartbeats 2200000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
variable {I X Y : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]
variable [MeasurableSpace X] [MeasurableSpace Y]

theorem mixtureKernel_dirac (i : I) (L : I → Kernel X Y) : mixtureKernel (Measure.dirac i) L = L i := by
  apply Kernel.ext
  intro x
  apply Measure.ext
  intro A hA
  rw [mixtureKernel_apply _ _ _ hA, lintegral_dirac' _ (measurable_of_countable _)]

namespace OracleProgram
variable {dx dy : ℕ} {X Y Z : Type} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

def pure (f : X → Y) (hf : Measurable f) : OracleProgram dx dy X Y where
  Seed := Unit
  seedLaw := Measure.dirac ()
  State := X
  machine _ := {
    query := fun _ _ => 0
    update := fun _ => Prod.fst
    output := fun _ _ => 0
    query_measurable := fun _ => measurable_const
    update_measurable := fun _ => measurable_fst
    output_measurable := fun _ => measurable_const }
  init _ := id
  init_measurable _ := measurable_id
  read _ := f
  read_measurable _ := hf
  calls _ := 0

theorem pure_law (f : X → Y) (hf : Measurable f) (K : Kernel (Joint dx dy) (Joint dx dy)) :
    (pure (dx := dx) (dy := dy) f hf).lawKernel K = taggedKernel (Kernel.deterministic f hf) 0 := by
  change mixtureKernel (Measure.dirac ()) ((pure f hf).branchKernel K) = _
  rw [mixtureKernel_dirac]
  change taggedKernel ((Kernel.deterministic id measurable_id).map f) 0 = _
  rw [Kernel.deterministic_map _ hf]
  rfl

def map (P : OracleProgram dx dy X Y) (f : Y → Z) (hf : Measurable f) : OracleProgram dx dy X Z where
  Seed := P.Seed
  seedLaw := P.seedLaw
  State := P.State
  machine := P.machine
  init := P.init
  init_measurable := P.init_measurable
  read i := f ∘ P.read i
  read_measurable i := hf.comp (P.read_measurable i)
  calls := P.calls

theorem branchKernel_apply (P : OracleProgram dx dy X Y) (K : Kernel (Joint dx dy) (Joint dx dy))
    (i : P.Seed) (x : X) : P.branchKernel K i x =
      ((P.machine i).runKernel (P.init i) (P.init_measurable i) K (P.calls i) x).map
        (fun s => (P.read i s, P.calls i)) := by
  rw [branchKernel, taggedKernel, ← Kernel.map_comp_right _ (f := P.read i)
    (g := fun y : Y => (y, P.calls i)) (P.read_measurable i) (measurable_id.prodMk measurable_const),
    Kernel.map_apply (f := (fun y : Y => (y, P.calls i)) ∘ P.read i) _
      ((P.read_measurable i).prodMk measurable_const)]
  rfl

theorem map_branch (P : OracleProgram dx dy X Y) (f : Y → Z) (hf : Measurable f)
    (K : Kernel (Joint dx dy) (Joint dx dy)) (i : P.Seed) :
    (P.map f hf).branchKernel K i = (P.branchKernel K i).map (fun z => (f z.1, z.2)) := by
  apply Kernel.ext
  intro x
  rw [branchKernel_apply, Kernel.map_apply (f := fun z : Y × ℕ => (f z.1, z.2)) _
    ((hf.comp measurable_fst).prodMk measurable_snd), branchKernel_apply,
    Measure.map_map (f := fun s => (P.read i s, P.calls i)) (g := fun z : Y × ℕ => (f z.1, z.2))
      ((hf.comp measurable_fst).prodMk measurable_snd) ((P.read_measurable i).prodMk measurable_const)]
  rfl

theorem map_law (P : OracleProgram dx dy X Y) (f : Y → Z) (hf : Measurable f)
    (K : Kernel (Joint dx dy) (Joint dx dy)) :
    (P.map f hf).lawKernel K = (P.lawKernel K).map (fun z => (f z.1, z.2)) := by
  change mixtureKernel P.seedLaw ((P.map f hf).branchKernel K) = (mixtureKernel P.seedLaw (P.branchKernel K)).map _
  rw [mixtureKernel_map _ _ (fun z : Y × ℕ => (f z.1, z.2)) ((hf.comp measurable_fst).prodMk measurable_snd)]
  congr 1
  funext i
  exact P.map_branch f hf K i

def iterate (P : OracleProgram dx dy X X) : ℕ → OracleProgram dx dy X X
  | 0 => pure id measurable_id
  | n + 1 => (P.iterate n).chain P

theorem iterate_law (P : OracleProgram dx dy X X) (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K]
    (n : ℕ) : (P.iterate n).lawKernel K = costedIterate (P.lawKernel K) n := by
  induction n with
  | zero => rw [iterate, pure_law]; rfl
  | succ n ih => rw [iterate, chain_law, ih, costedIterate]

theorem iterate_original (P : OracleProgram dx dy X X) (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K]
    (n : ℕ) : (P.iterate n).originalKernel K = costedIterate (P.originalKernel K) n := by
  rw [originalKernel_eq_law, iterate_law, P.originalKernel_eq_law]

end OracleProgram
end FreshGradientMinimax
