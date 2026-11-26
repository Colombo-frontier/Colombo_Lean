import SecondOrder.OracleSeedTransport

open MeasureTheory

namespace SecondOrder
namespace OracleProgram
noncomputable section

variable {Q Y O Ω S : Type}

theorem runDraws_append_output_of_usesAtMost (q₀ : Q) (o₀ : O) (a₀ : Ω)
    (reply : Q → Ω → Y) {p : OracleProgram Q Y O} {N : ℕ} (hp : UsesAtMost N p)
    (M : ℕ) (u : Draws Ω N) (v : Draws Ω M) :
    output o₀ (runDraws q₀ reply p (N+M) (drawsAppend N M u v))=
      output o₀ (runDraws q₀ reply p N u) := by
  obtain ⟨o,ho⟩ := runDraws_done q₀ reply a₀ hp u
  rw [runDraws_append,ho,runDraws_done_program]

variable [MeasurableSpace Q] [MeasurableSpace Y] [MeasurableSpace O]
  [MeasurableSpace Ω] [MeasurableSpace S]

/-- Padding a uniformly bounded program with fresh samples changes no
output probability. This also holds jointly with arbitrary private seeds. -/
theorem seededOutputLaw_add_of_usesAtMost (μ : Measure Ω) (η : Measure S)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure η]
    (q₀ : Q) (y₀ : Y) (o₀ : O) (a₀ : Ω) (reply : Q → Ω → Y)
    (hr : Measurable (fun w : Q × Ω => reply w.1 w.2))
    (p : S → OracleProgram Q Y O) (hp : MeasurableFamily q₀ o₀ p)
    (N : ℕ) (hN : ∀ s, UsesAtMost N (p s)) (M : ℕ) :
    seededOutputLaw μ η q₀ o₀ reply p (N+M)=seededOutputLaw μ η q₀ o₀ reply p N := by
  have hcat := (MeasurePreserving.id η).prod (drawsAppend_measurePreserving μ N M)
  have hfst : MeasurePreserving (Prod.fst : Draws Ω N × Draws Ω M → Draws Ω N)
      ((drawsLaw μ N).prod (drawsLaw μ M)) (drawsLaw μ N) := by
    refine ⟨measurable_fst,?_⟩
    simp only [Measure.map_fst_prod,measure_univ,one_smul]
  have hdrop := (MeasurePreserving.id η).prod hfst
  have hm := hp.runDrawsOutput y₀ a₀ reply hr (N+M)
  have hn := hp.runDrawsOutput y₀ a₀ reply hr N
  unfold seededOutputLaw
  rw [←hcat.map_eq,Measure.map_map hm hcat.measurable,←hdrop.map_eq,Measure.map_map hn hdrop.measurable]
  apply congrArg (fun g : S × (Draws Ω N × Draws Ω M) → O =>
    Measure.map g (η.prod ((drawsLaw μ N).prod (drawsLaw μ M))))
  funext w
  exact runDraws_append_output_of_usesAtMost q₀ o₀ a₀ reply (hN w.1) M w.2.1 w.2.2

theorem seededOutputLaw_of_budget_le (μ : Measure Ω) (η : Measure S)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure η]
    (q₀ : Q) (y₀ : Y) (o₀ : O) (a₀ : Ω) (reply : Q → Ω → Y)
    (hr : Measurable (fun w : Q × Ω => reply w.1 w.2))
    (p : S → OracleProgram Q Y O) (hp : MeasurableFamily q₀ o₀ p)
    (N : ℕ) (hN : ∀ s, UsesAtMost N (p s)) (M : ℕ) (hNM : N≤M) :
    seededOutputLaw μ η q₀ o₀ reply p M=seededOutputLaw μ η q₀ o₀ reply p N := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hNM
  exact seededOutputLaw_add_of_usesAtMost μ η q₀ y₀ o₀ a₀ reply hr p hp N hN k

end
end OracleProgram
end SecondOrder
