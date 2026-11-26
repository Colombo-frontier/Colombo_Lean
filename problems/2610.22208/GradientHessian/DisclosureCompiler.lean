import GradientHessian.OracleControl
import GradientHessian.ReadoutOracle
import GradientHessian.OracleSimulation

/-! Preprocessing with two separate hard caps: ordinary products and prior
readout disclosures. A disclosure is computed by a finite oracle procedure. -/

namespace GradientHessian.DisclosureCompiler
open Matrix MeasureTheory LowRank OracleComposition
noncomputable section

structure Program (d : ℕ) (State : Type*) [MeasurableSpace State] where
  mode : State → Fin 4
  think : State → State
  query : State → Fin d → ℝ
  mark : State → Fin d → ℝ
  next : State × (Fin d → ℝ) → State
  disclosed : State × (Fin d → ℝ) → State
  mode_measurable : Measurable mode
  think_measurable : Measurable think
  query_measurable : Measurable query
  mark_measurable : Measurable mark
  next_measurable : Measurable next
  disclosed_measurable : Measurable disclosed

variable {d m : ℕ} {State : Type*} [MeasurableSpace State]

def Program.flag (P : Program d State) (i : Fin 4) : MeasurableStateMap State Bool :=
  ⟨fun s => if P.mode s = i then true else false,
    Measurable.ite (P.mode_measurable (measurableSet_singleton i)) measurable_const measurable_const⟩

def Program.terminal (P : Program d State) : MeasurableStateMap State (Bool × State) :=
  ⟨fun s => ((P.flag 0).1 s, s), (P.flag 0).2.prodMk measurable_id⟩

def Program.eval (P : Program d State) (A : Matrix (Fin d) (Fin d) ℝ)
    (readout : (Fin d → ℝ) → Fin d → ℝ) : ℕ → State → Bool × State
  | 0, s => P.terminal.1 s
  | n+1, s => if P.mode s = 0 then P.terminal.1 s
      else if P.mode s = 1 then P.eval A readout n (P.think s)
      else if P.mode s = 2 then P.eval A readout n (P.next (s, A *ᵥ P.query s))
      else P.eval A readout n (P.disclosed (s, readout (P.mark s)))

def Program.ordinaryCalls (P : Program d State) (A : Matrix (Fin d) (Fin d) ℝ)
    (readout : (Fin d → ℝ) → Fin d → ℝ) : ℕ → State → ℕ
  | 0, _ => 0
  | n+1, s => if P.mode s = 0 then 0
      else if P.mode s = 1 then P.ordinaryCalls A readout n (P.think s)
      else if P.mode s = 2 then P.ordinaryCalls A readout n (P.next (s, A *ᵥ P.query s)) + 1
      else P.ordinaryCalls A readout n (P.disclosed (s, readout (P.mark s)))

def Program.disclosures (P : Program d State) (A : Matrix (Fin d) (Fin d) ℝ)
    (readout : (Fin d → ℝ) → Fin d → ℝ) : ℕ → State → ℕ
  | 0, _ => 0
  | n+1, s => if P.mode s = 0 then 0
      else if P.mode s = 1 then P.disclosures A readout n (P.think s)
      else if P.mode s = 2 then P.disclosures A readout n (P.next (s, A *ᵥ P.query s))
      else P.disclosures A readout n (P.disclosed (s, readout (P.mark s))) + 1

def Program.compile (P : Program d State)
    (readout : Procedure d m (Fin d → ℝ) (Fin d → ℝ)) :
    (n q₀ S : ℕ) → Procedure d (q₀ + S*m) State (Bool × State)
  | 0, q₀, S => Procedure.idle d (q₀+S*m) P.terminal
  | n+1, q₀, S =>
    let stop := Procedure.idle d (q₀+S*m) P.terminal
    let think := (P.compile readout n q₀ S).comap ⟨P.think, P.think_measurable⟩
    let query := match q₀ with
      | 0 => Procedure.idle d (0+S*m)
          ⟨fun s : State => (false,s), measurable_const.prodMk measurable_id⟩
      | q+1 =>
        ((((Procedure.product d).comap ⟨P.query,P.query_measurable⟩).withSeed).bind
          ((P.compile readout n q S).comap ⟨P.next,P.next_measurable⟩)).castBudget (by omega)
    let disclose := match S with
      | 0 => Procedure.idle d (q₀+0*m)
          ⟨fun s : State => (false,s), measurable_const.prodMk measurable_id⟩
      | s+1 =>
        (((readout.comap ⟨P.mark,P.mark_measurable⟩).withSeed).bind
          ((P.compile readout n q₀ s).comap ⟨P.disclosed,P.disclosed_measurable⟩)).castBudget
            (by rw [Nat.succ_mul]; omega)
    Procedure.choose (P.flag 0) stop
      (Procedure.choose (P.flag 1) think (Procedure.choose (P.flag 2) query disclose))

theorem Program.compile_calls (P : Program d State)
    (readout : Procedure d m (Fin d → ℝ) (Fin d → ℝ)) (n q₀ S : ℕ)
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (s : State) :
    ((P.compile readout n q₀ S).toProgram s).calls oracle = q₀ + S*m :=
  Procedure.calls_toProgram _ oracle s

theorem Program.compile_simulates (P : Program d State)
    (readout : Procedure d m (Fin d → ℝ) (Fin d → ℝ)) (n q₀ S : ℕ)
    (A : Matrix (Fin d) (Fin d) ℝ) (s : State)
    (hq : P.ordinaryCalls A (readout.run A) n s ≤ q₀)
    (hS : P.disclosures A (readout.run A) n s ≤ S) :
    (P.compile readout n q₀ S).run A s = P.eval A (readout.run A) n s := by
  induction n generalizing q₀ S s with
  | zero => simp only [Program.compile, Procedure.run_idle, Program.eval]
  | succ n ih =>
      by_cases h0 : P.mode s = 0
      · simp [Program.compile, Procedure.run_choose, Procedure.run_idle, Program.flag,
          Program.eval, h0]
      · by_cases h1 : P.mode s = 1
        · have hq' : P.ordinaryCalls A (readout.run A) n (P.think s) ≤ q₀ := by
            simpa [Program.ordinaryCalls,h0,h1] using hq
          have hS' : P.disclosures A (readout.run A) n (P.think s) ≤ S := by
            simpa [Program.disclosures,h0,h1] using hS
          simpa [Program.compile, Procedure.run_choose, Procedure.run_comap, Program.flag,
            Program.eval,h0,h1] using ih q₀ S (P.think s) hq' hS'
        · by_cases h2 : P.mode s = 2
          · have hq' : P.ordinaryCalls A (readout.run A) n (P.next (s,A*ᵥP.query s)) + 1 ≤ q₀ := by
              simpa [Program.ordinaryCalls,h0,h1,h2] using hq
            have hS' : P.disclosures A (readout.run A) n (P.next (s,A*ᵥP.query s)) ≤ S := by
              simpa [Program.disclosures,h0,h1,h2] using hS
            cases q₀ with
            | zero => omega
            | succ q =>
                have hq'' : P.ordinaryCalls A (readout.run A) n (P.next (s,A*ᵥP.query s)) ≤ q := by omega
                simpa [Program.compile,Procedure.run_choose,Program.flag,Program.eval,h0,h1,h2,
                  Procedure.run_castBudget,Procedure.run_bind,Procedure.run_withSeed,
                  Procedure.run_comap,Procedure.run_product] using ih q S _ hq'' hS'
          · have hq' : P.ordinaryCalls A (readout.run A) n
                (P.disclosed (s,readout.run A (P.mark s))) ≤ q₀ := by
              simpa [Program.ordinaryCalls,h0,h1,h2] using hq
            have hS' : P.disclosures A (readout.run A) n
                (P.disclosed (s,readout.run A (P.mark s))) + 1 ≤ S := by
              simpa [Program.disclosures,h0,h1,h2] using hS
            cases S with
            | zero => omega
            | succ S =>
                have hS'' : P.disclosures A (readout.run A) n
                    (P.disclosed (s,readout.run A (P.mark s))) ≤ S := by omega
                simpa [Program.compile,Procedure.run_choose,Program.flag,Program.eval,h0,h1,h2,
                  Procedure.run_castBudget,Procedure.run_bind,Procedure.run_withSeed,
                  Procedure.run_comap] using ih q₀ S _ hq' hS''

def readoutProcedure (M : ℝ) (P : Matrix (Fin d) (Fin d) ℝ) (fallback : Fin d → ℝ) :
    Procedure d (ReadoutFilter.degree M ReadoutFilter.delta) (Fin d → ℝ) (Fin d → ℝ) :=
  Procedure.ofBounded (ReadoutOracle.readoutPolicy M P fallback)

theorem run_readoutProcedure (M : ℝ) (P A : Matrix (Fin d) (Fin d) ℝ)
    (hA : Aᵀ = A) (fallback w : Fin d → ℝ) :
    (readoutProcedure M P fallback).run A w = ReadoutOracle.readout M P A fallback w := by
  rw [readoutProcedure,Procedure.run_ofBounded _ A hA]
  exact (ReadoutOracle.readoutPolicy_exact M P A fallback w).1

/-- The actual preprocessing execution with literal earlier readouts has
budget `q₀ + S*m_pol`. This equality includes stopping decisions made using
those readouts; no readout is supplied as matrix-dependent initial data. -/
theorem Program.literal_preprocessing_simulates (P : Program d State)
    (M : ℝ) (proj A : Matrix (Fin d) (Fin d) ℝ) (hA : Aᵀ = A)
    (fallback : Fin d → ℝ) (n q₀ S : ℕ) (s : State)
    (hq : P.ordinaryCalls A (ReadoutOracle.readout M proj A fallback) n s ≤ q₀)
    (hS : P.disclosures A (ReadoutOracle.readout M proj A fallback) n s ≤ S) :
    (P.compile (readoutProcedure M proj fallback) n q₀ S).run A s =
      P.eval A (ReadoutOracle.readout M proj A fallback) n s := by
  have he : (readoutProcedure M proj fallback).run A = ReadoutOracle.readout M proj A fallback :=
    funext (run_readoutProcedure M proj A hA fallback)
  simpa only [he] using P.compile_simulates (readoutProcedure M proj fallback) n q₀ S A s
    (by simpa only [he] using hq) (by simpa only [he] using hS)

/-- On every symmetric oracle matrix, synthesis and the source transformation
give the original finite preprocessing output. The compiler's hard call cap
holds on every counterfactual oracle, separately from these preservation caps. -/
theorem Program.source_preprocessing_simulates (P : Program d State)
    (M scale : ℝ) (proj D W : Matrix (Fin d) (Fin d) ℝ)
    (hD : Dᵀ = D) (hW : Wᵀ = W) (fallback : Fin d → ℝ) (n q₀ S : ℕ) (s : State)
    (hq : P.ordinaryCalls (MatrixSandwichOracle.transformedMatrix scale D W)
      (ReadoutOracle.readout M proj (MatrixSandwichOracle.transformedMatrix scale D W) fallback)
      n s ≤ q₀)
    (hS : P.disclosures (MatrixSandwichOracle.transformedMatrix scale D W)
      (ReadoutOracle.readout M proj (MatrixSandwichOracle.transformedMatrix scale D W) fallback)
      n s ≤ S) :
    (OracleSimulation.procedure scale D
      (P.compile (readoutProcedure M proj fallback) n q₀ S)).run W s =
      P.eval (MatrixSandwichOracle.transformedMatrix scale D W)
        (ReadoutOracle.readout M proj (MatrixSandwichOracle.transformedMatrix scale D W) fallback) n s := by
  rw [OracleSimulation.run_procedure]
  exact P.literal_preprocessing_simulates M proj _
    (MatrixSandwichOracle.transformedMatrix_symmetric scale D W hD hW) fallback n q₀ S s hq hS

theorem Program.source_preprocessing_calls (P : Program d State)
    (M scale : ℝ) (proj D : Matrix (Fin d) (Fin d) ℝ)
    (fallback : Fin d → ℝ) (n q₀ S : ℕ)
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (s : State) :
    ((OracleSimulation.procedure scale D
      (P.compile (readoutProcedure M proj fallback) n q₀ S)).toProgram s).calls oracle =
        q₀+S*ReadoutFilter.degree M ReadoutFilter.delta :=
  Procedure.calls_toProgram _ oracle s

end
end GradientHessian.DisclosureCompiler
