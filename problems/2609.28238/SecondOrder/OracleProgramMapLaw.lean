import SecondOrder.OracleProgramSeededKernel

open MeasureTheory

namespace SecondOrder
namespace OracleProgram
noncomputable section

variable {Q Y O O' Ω S : Type}

theorem runDraws_bind_done (q₀ : Q) (reply : Q → Ω → Y)
    (p : OracleProgram Q Y O) (g : O → O') (N : ℕ) (w : Draws Ω N) :
    runDraws q₀ reply (bind p (fun o => .done (g o))) N w=
      bind (runDraws q₀ reply p N w) (fun o => .done (g o)) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    simp only [runDraws,ih w.1]
    cases runDraws q₀ reply p N w.1 <;> rfl

variable [MeasurableSpace Q] [MeasurableSpace Y] [MeasurableSpace O]
  [MeasurableSpace O'] [MeasurableSpace Ω] [MeasurableSpace S]

theorem seededOutputLaw_const (μ : Measure Ω) (η : Measure S)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure η]
    (q₀ : Q) (y₀ : Y) (o₀ : O) (a₀ : Ω) (reply : Q → Ω → Y)
    (hr : Measurable (fun w : Q × Ω => reply w.1 w.2))
    (p : OracleProgram Q Y O) (hp : MeasurableFamily q₀ o₀ (fun _ : Unit => p)) (N : ℕ) :
    seededOutputLaw μ η q₀ o₀ reply (fun _ => p) N=outputLaw μ q₀ o₀ reply p N := by
  have hp' := hp.comp (fun _ : S => ()) measurable_const
  rw [seededOutputLaw_eq_bind μ η q₀ y₀ o₀ a₀ reply hr _ hp' N]
  change η.bind (fun _ => outputLaw μ q₀ o₀ reply p N)=_
  simp

theorem outputLaw_bind_done (μ : Measure Ω)
    (q₀ : Q) (y₀ : Y) (o₀ : O) (o₀' : O') (a₀ : Ω) (reply : Q → Ω → Y)
    (hr : Measurable (fun w : Q × Ω => reply w.1 w.2))
    (p : OracleProgram Q Y O) (hp : MeasurableFamily q₀ o₀ (fun _ : Unit => p))
    (N : ℕ) (hN : UsesAtMost N p) (g : O → O') (hg : Measurable g) :
    outputLaw μ q₀ o₀' reply (bind p (fun o => .done (g o))) N=
      Measure.map g (outputLaw μ q₀ o₀ reply p N) := by
  unfold outputLaw
  rw [Measure.map_map hg (hp.outputRun y₀ a₀ reply hr N ())]
  apply congrArg (fun k : Draws Ω N → O' => Measure.map k (drawsLaw μ N))
  funext w
  obtain ⟨o,ho⟩ := runDraws_done q₀ reply a₀ hN w
  simp only [runDraws_bind_done,ho,bind_done,output,Function.comp_apply]

theorem seededOutputLaw_bind_done (μ : Measure Ω) (η : Measure S)
    (q₀ : Q) (y₀ : Y) (o₀ : O) (o₀' : O') (a₀ : Ω) (reply : Q → Ω → Y)
    (hr : Measurable (fun w : Q × Ω => reply w.1 w.2))
    (p : S → OracleProgram Q Y O) (hp : MeasurableFamily q₀ o₀ p)
    (N : ℕ) (hN : ∀ s, UsesAtMost N (p s)) (g : O → O') (hg : Measurable g) :
    seededOutputLaw μ η q₀ o₀' reply (fun s => bind (p s) (fun o => .done (g o))) N=
      Measure.map g (seededOutputLaw μ η q₀ o₀ reply p N) := by
  unfold seededOutputLaw
  rw [Measure.map_map hg (hp.runDrawsOutput y₀ a₀ reply hr N)]
  apply congrArg (fun k : S × Draws Ω N → O' => Measure.map k (η.prod (drawsLaw μ N)))
  funext w
  obtain ⟨o,ho⟩ := runDraws_done q₀ reply a₀ (hN w.1) w.2
  simp only [runDraws_bind_done,ho,bind_done,output,Function.comp_apply]

theorem outputLaw_of_budget_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q₀ : Q) (y₀ : Y) (o₀ : O) (a₀ : Ω) (reply : Q → Ω → Y)
    (hr : Measurable (fun w : Q × Ω => reply w.1 w.2))
    (p : OracleProgram Q Y O) (hp : MeasurableFamily q₀ o₀ (fun _ : Unit => p))
    (N : ℕ) (hN : UsesAtMost N p) (M : ℕ) (hNM : N≤M) :
    outputLaw μ q₀ o₀ reply p M=outputLaw μ q₀ o₀ reply p N := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hNM
  exact outputLaw_add_of_usesAtMost μ q₀ y₀ o₀ a₀ reply hr _ hp N () hN k

theorem seededOutputLaw_done_family (μ : Measure Ω) (η : Measure S)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure η]
    (q₀ : Q) (o₀ : O) (reply : Q → Ω → Y) (g : S → O) (hg : Measurable g) (N : ℕ) :
    seededOutputLaw μ η q₀ o₀ reply (fun s => .done (g s)) N=Measure.map g η := by
  have he : Measure.map (Prod.fst : S × Draws Ω N → S) (η.prod (drawsLaw μ N))=η := by
    simp only [Measure.map_fst_prod,measure_univ,one_smul]
  unfold seededOutputLaw
  simp only [runDraws_done_program,output]
  conv_rhs => rw [←he,Measure.map_map hg measurable_fst]
  rfl


end
end OracleProgram
end SecondOrder
