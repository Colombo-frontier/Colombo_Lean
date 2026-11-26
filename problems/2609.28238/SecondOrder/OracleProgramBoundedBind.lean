import SecondOrder.OracleProgramFirstStep

open MeasureTheory ProbabilityTheory

namespace SecondOrder
namespace OracleProgram
noncomputable section

variable {Q Y O O' Ω : Type} [MeasurableSpace Q] [MeasurableSpace Y]
  [MeasurableSpace O] [MeasurableSpace O'] [MeasurableSpace Ω]

theorem outputLaw_done (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q₀ : Q) (o₀ o : O) (reply : Q → Ω → Y) (N : ℕ) :
    outputLaw μ q₀ o₀ reply (.done o) N=Measure.dirac o := by
  unfold outputLaw
  simp only [runDraws_done_program,output]
  simp

/-- Bounded adaptive stopping preserves fresh sampling at the boundary
between subprograms. The first program need not use a fixed call count. -/
theorem outputLaw_bind_of_usesAtMost (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q₀ : Q) (y₀ : Y) (o₀ : O) (o₀' : O') (a₀ : Ω) (reply : Q → Ω → Y)
    (hr : Measurable (fun w : Q × Ω => reply w.1 w.2))
    (p : OracleProgram Q Y O) (hp : MeasurableFamily q₀ o₀ (fun _ : Unit => p))
    (N : ℕ) (hN : UsesAtMost N p)
    (f : O → OracleProgram Q Y O') (hf : MeasurableFamily q₀ o₀' f)
    (M : ℕ) (hM : ∀ o, UsesAtMost M (f o)) :
    outputLaw μ q₀ o₀' reply (bind p f) (N+M)=
      (outputLaw μ q₀ o₀ reply p N).bind (outputKernel μ q₀ y₀ o₀' a₀ reply hr f hf M) := by
  let K := outputKernel μ q₀ y₀ o₀' a₀ reply hr f hf M
  change outputLaw μ q₀ o₀' reply (bind p f) (N+M)=(outputLaw μ q₀ o₀ reply p N).bind K
  induction N generalizing p with
  | zero =>
    cases p with
    | done o =>
      rw [bind_done,Nat.zero_add,outputLaw_done,Measure.dirac_bind K.measurable]
      rfl
    | request q k => exact False.elim hN
  | succ N ih =>
    cases p with
    | done o =>
      rw [bind_done,outputLaw_done,Measure.dirac_bind K.measurable]
      change outputLaw μ q₀ o₀' reply (f o) (N+1+M)=outputLaw μ q₀ o₀' reply (f o) M
      rw [Nat.add_comm (N+1) M]
      exact outputLaw_add_of_usesAtMost μ q₀ y₀ o₀' a₀ reply hr f hf M o (hM o) (N+1)
    | request q k =>
      have hf' := hf.comp (fun w : Unit × O => w.2) measurable_snd
      have hfull := hp.bind (f := fun (_ : Unit) o => f o) hf'
      ext e he
      rw [show N+1+M=(N+M)+1 by omega,
        outputLaw_first_step_apply μ q₀ y₀ o₀' a₀ reply hr
          (fun _ : Unit => bind (.request q k) f) hfull (N+M) () e he,
        Measure.bind_apply he K.measurable.aemeasurable,
        lintegral_outputLaw_first_step μ q₀ y₀ o₀ a₀ reply hr
          (fun _ : Unit => .request q k) hp N () (fun o => K o e) (K.measurable_coe he)]
      apply lintegral_congr
      intro z
      have hk := hp.advance.comp (fun _ : Unit => ((),reply q z)) measurable_const
      have hh := ih (p := k (reply q z)) hk (hN (reply q z))
      change outputLaw μ q₀ o₀' reply (bind (k (reply q z)) f) (N+M) e=
        ∫⁻ o, K o e ∂outputLaw μ q₀ o₀ reply (k (reply q z)) N
      rw [hh,Measure.bind_apply he K.measurable.aemeasurable]

end
end OracleProgram
end SecondOrder
