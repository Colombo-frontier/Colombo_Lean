import Bilevel.OracleMachineRun
import Bilevel.OracleSigmaSpace

/-! Countable measurable dispatch chooses an actual finite computation from
the public input. The tagged machine does not inspect future oracle draws. -/
noncomputable section
open MeasureTheory
namespace Bilevel.OracleCode.Machine
open BorelAdaptive
variable {Q O A B : Space}

def choose (p : ℕ → Machine Q O A B) (n : A → ℕ) (hn : Measurable n) : Machine Q O A B where
  state := of (Σ i,(p i).state)
  start := fun a => ⟨n a,(p (n a)).start a⟩
  start_measurable := by
    have hm : Measurable (fun z : A × ℕ => (⟨z.2,(p z.2).start z.1⟩ : Σ i,(p i).state)) :=
      measurable_from_prod_countable (fun i => (OracleSigma.mk_measurable i).comp (p i).start_measurable)
    exact hm.comp (measurable_id.prodMk hn)
  program := {
    query := fun z => (p z.1).program.query z.2
    query_measurable := OracleSigma.elim_measurable _ (fun i => (p i).program.query_measurable)
    update := fun z => ⟨z.1.1,(p z.1.1).program.update (z.1.2,z.2)⟩
    update_measurable := OracleSigma.prod_elim_measurable _ (fun i =>
      (OracleSigma.mk_measurable i).comp (p i).program.update_measurable)
    halt := fun z => (p z.1).program.halt z.2
    halt_measurable := OracleSigma.elim_measurable _ (fun i => (p i).program.halt_measurable)
    output := fun z => (p z.1).program.output z.2
    output_measurable := OracleSigma.elim_measurable _ (fun i => (p i).program.output_measurable) }

theorem choose_run {Seed : Type*} (p : ℕ → Machine Q O A B) (n : A → ℕ) (hn : Measurable n)
    (response : Q → Seed → O) (s : ℕ → Seed) (i : ℕ) (u : (p i).state) (k : ℕ) :
    run (choose p n hn).program (fun _ : Unit => response) () s ⟨i,u⟩ k=
      ⟨i,run (p i).program (fun _ : Unit => response) () s u k⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [run,ih,run]
      simp only [step,choose]
      split <;> rfl

theorem choose_correct (p : ℕ → Machine Q O A B) (c : ℕ → Code Q O A B)
    (hp : ∀ i,Correct (p i) (c i)) (n : A → ℕ) (hn : Measurable n) :
    Correct (choose p n hn) (.choose c n hn) := by
  intro Seed response s a
  have h := hp (n a) Seed response s a
  have he (k : ℕ) : execute (choose p n hn) response s a k=
      ⟨n a,execute (p (n a)) response s a k⟩ := choose_run p n hn response s (n a) ((p (n a)).start a) k
  change _ ∧ _ ∧ _
  simp only [eval]
  simp_rw [he]
  exact h

end Bilevel.OracleCode.Machine
