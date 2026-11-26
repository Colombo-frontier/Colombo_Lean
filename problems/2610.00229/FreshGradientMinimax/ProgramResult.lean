import FreshGradientMinimax.ProgramUpdate

/-! Output marginal of an original-query program. These identities let
adaptive program composition reuse unconditional input-law estimates. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
namespace OracleProgram
variable {dx dy : ℕ} {X Y Z W : Type}
variable [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z] [MeasurableSpace W]

def resultKernel (P : OracleProgram dx dy X Y) (K : Kernel (Joint dx dy) (Joint dx dy)) : Kernel X Y :=
  (P.lawKernel K).map Prod.fst

instance resultKernel_markov (P : OracleProgram dx dy X Y) (K : Kernel (Joint dx dy) (Joint dx dy))
    [IsMarkovKernel K] : IsMarkovKernel (P.resultKernel K) := Kernel.IsMarkovKernel.map _ measurable_fst

theorem original_result_law (P : OracleProgram dx dy X Y) (K : Kernel (Joint dx dy) (Joint dx dy))
    [IsMarkovKernel K] (ν : Measure X) : (P.originalKernel K ∘ₘ ν).map Prod.fst = P.resultKernel K ∘ₘ ν := by
  rw [originalKernel_eq_law, Measure.map_comp _ _ measurable_fst]
  rfl

theorem pure_result (f : X → Y) (hf : Measurable f) (K : Kernel (Joint dx dy) (Joint dx dy)) :
    (pure (dx := dx) (dy := dy) f hf).resultKernel K = Kernel.deterministic f hf := by
  rw [resultKernel, pure_law, taggedKernel_first]

theorem map_result (P : OracleProgram dx dy X Y) (f : Y → Z) (hf : Measurable f)
    (K : Kernel (Joint dx dy) (Joint dx dy)) : (P.map f hf).resultKernel K = (P.resultKernel K).map f := by
  rw [resultKernel, map_law, ← Kernel.map_comp_right _ (f := fun z : Y × ℕ => (f z.1, z.2))
    (g := Prod.fst) ((hf.comp measurable_fst).prodMk measurable_snd) measurable_fst,
    resultKernel, ← Kernel.map_comp_right _ measurable_fst hf]
  rfl

theorem chain_result (P : OracleProgram dx dy X Y) (Q : OracleProgram dx dy Y Z)
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] :
    (P.chain Q).resultKernel K = Q.resultKernel K ∘ₖ P.resultKernel K := by
  rw [resultKernel, chain_law, costedCompose_first]
  rfl

theorem precompose_result (P : OracleProgram dx dy X Y) (f : W → X) (hf : Measurable f)
    (K : Kernel (Joint dx dy) (Joint dx dy)) :
    (P.precompose f hf).resultKernel K = (P.resultKernel K).comap f hf := by
  rw [resultKernel, precompose_law, ← Kernel.comap_map_comm _ hf measurable_fst]
  rfl

end OracleProgram
end FreshGradientMinimax
