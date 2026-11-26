import LowRank.GaussianModel

/-! Finite adaptive oracle programs, and cost-preserving simulations.
An arbitrary random seed may select a program; the simulation is pointwise in it. -/

namespace LowRank

inductive OracleProgram (Q R O : Type*) where
  | done : O → OracleProgram Q R O
  | ask : Q → (R → OracleProgram Q R O) → OracleProgram Q R O

namespace OracleProgram
variable {Q R O Q' R' : Type*}

def eval (oracle : Q → R) : OracleProgram Q R O → O
  | .done o => o
  | .ask v next => (next (oracle v)).eval oracle

def calls (oracle : Q → R) : OracleProgram Q R O → ℕ
  | .done _ => 0
  | .ask v next => (next (oracle v)).calls oracle + 1

def HasBudget : ℕ → OracleProgram Q R O → Prop
  | _, .done _ => True
  | 0, .ask _ _ => False
  | q + 1, .ask _ next => ∀ r, (next r).HasBudget q

def simulate (encode : Q → Q') (decode : Q → R' → R) :
    OracleProgram Q R O → OracleProgram Q' R' O
  | .done o => .done o
  | .ask v next => .ask (encode v) (fun r => (next (decode v r)).simulate encode decode)

theorem eval_simulate (oracle : Q → R) (oracle' : Q' → R')
    (encode : Q → Q') (decode : Q → R' → R)
    (h : ∀ v, decode v (oracle' (encode v)) = oracle v)
    (p : OracleProgram Q R O) :
    (p.simulate encode decode).eval oracle' = p.eval oracle := by
  induction p with
  | done o => rfl
  | ask v next ih => simp only [simulate, eval, h, ih]

theorem calls_simulate (oracle : Q → R) (oracle' : Q' → R')
    (encode : Q → Q') (decode : Q → R' → R)
    (h : ∀ v, decode v (oracle' (encode v)) = oracle v)
    (p : OracleProgram Q R O) :
    (p.simulate encode decode).calls oracle' = p.calls oracle := by
  induction p with
  | done o => rfl
  | ask v next ih => simp only [simulate, calls, h, ih]

theorem budget_simulate (encode : Q → Q') (decode : Q → R' → R)
    {q : ℕ} {p : OracleProgram Q R O} (hp : p.HasBudget q) :
    (p.simulate encode decode).HasBudget q := by
  induction q generalizing p with
  | zero => cases p <;> simp_all [HasBudget, simulate]
  | succ q ih =>
    cases p with
    | done o => trivial
    | ask v next => exact fun r => ih (hp (decode v r))

theorem calls_le_budget (oracle : Q → R) {q : ℕ} {p : OracleProgram Q R O}
    (hp : p.HasBudget q) : p.calls oracle ≤ q := by
  induction q generalizing p with
  | zero => cases p <;> simp_all [HasBudget, calls]
  | succ q ih =>
    cases p with
    | done o => simp [calls]
    | ask v next => exact Nat.add_le_add_right (ih (hp (oracle v))) 1

end OracleProgram

open Matrix
open scoped Matrix

def twoSidedOracle {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (query : Bool × (Fin d → ℝ)) : Fin d → ℝ :=
  if query.1 then Aᵀ *ᵥ query.2 else A *ᵥ query.2

theorem symmetric_twoSidedOracle {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}
    (hA : Aᵀ = A) (v : Bool × (Fin d → ℝ)) :
    twoSidedOracle A v = A *ᵥ v.2 := by simp [twoSidedOracle, hA]

/-- Every finite adaptive two-sided algorithm for `H` can be executed with one
`W` query for each original query, with the exact same output. -/
theorem hardMatrix_program_simulation {d : ℕ} {O : Type*}
    (L : ℝ) (W : Matrix (Fin d) (Fin d) ℝ) (hW : Wᵀ = W)
    (p : OracleProgram (Bool × (Fin d → ℝ)) (Fin d → ℝ) O) :
    let encode : Bool × (Fin d → ℝ) → (Fin d → ℝ) := Prod.snd
    let decode := fun (v : Bool × (Fin d → ℝ)) (r : Fin d → ℝ) => v.2 - L⁻¹ • r
    (p.simulate encode decode).eval (fun v => W *ᵥ v) = p.eval (twoSidedOracle (hardMatrix L W)) ∧
    (p.simulate encode decode).calls (fun v => W *ᵥ v) = p.calls (twoSidedOracle (hardMatrix L W)) := by
  dsimp
  have h : ∀ v : Bool × (Fin d → ℝ),
      v.2 - L⁻¹ • (W *ᵥ v.2) = twoSidedOracle (hardMatrix L W) v := by
    intro v
    rw [symmetric_twoSidedOracle (hardMatrix_symmetric L hW), hardMatrix_matvec]
  exact ⟨OracleProgram.eval_simulate (twoSidedOracle (hardMatrix L W))
      (fun v => W *ᵥ v) Prod.snd (fun v r => v.2 - L⁻¹ • r) h p,
    OracleProgram.calls_simulate (twoSidedOracle (hardMatrix L W))
      (fun v => W *ᵥ v) Prod.snd (fun v r => v.2 - L⁻¹ • r) h p⟩

end LowRank
