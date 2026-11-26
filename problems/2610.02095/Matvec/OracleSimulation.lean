import Matvec.GameAlgebra

/-!
# Hard-capped adaptive oracle programs and exact query compilation

Queries and terminal outputs may depend on the entire preceding transcript.
The natural-number index bounds all branches, including transcripts outside
the promised matrix class. No restriction to Krylov vectors, feasible query
vectors, or queried terminal outputs is imposed.

This file proves deterministic, seedwise simulation. Probability spaces and
measurability of randomized program selection are separate obligations.
-/

namespace Matvec

universe u v w u' v'

/-- A finite adaptive program with an all-transcript query cap. `pure` permits
early stopping and arbitrary terminal output. -/
inductive QueryProgram (Query : Type u) (Reply : Type v) (Output : Type w) : ℕ → Type (max u v w)
  | pure {k : ℕ} (output : Output) : QueryProgram Query Reply Output k
  | query {k : ℕ} (q : Query) (next : Reply → QueryProgram Query Reply Output k) :
      QueryProgram Query Reply Output (k + 1)

namespace QueryProgram

variable {Q : Type u} {R : Type v} {O : Type w}
  {Q' : Type u'} {R' : Type v'}

def eval (oracle : Q → R) : {k : ℕ} → QueryProgram Q R O k → O
  | _, .pure output => output
  | _, .query q next => eval oracle (next (oracle q))

def queryCount (oracle : Q → R) : {k : ℕ} → QueryProgram Q R O k → ℕ
  | _, .pure _ => 0
  | _, .query q next => 1 + queryCount oracle (next (oracle q))

/-- Count against arbitrary time-dependent replies, including inconsistent
replies to repeated queries. This witnesses the all-transcript hard cap. -/
def transcriptQueryCount (replies : ℕ → Q → R) (round : ℕ) :
    {k : ℕ} → QueryProgram Q R O k → ℕ
  | _, .pure _ => 0
  | _, .query q next => 1 + transcriptQueryCount replies (round + 1)
      (next (replies round q))

theorem queryCount_le (oracle : Q → R) {k : ℕ} (p : QueryProgram Q R O k) :
    p.queryCount oracle ≤ k := by
  induction p with
  | pure output => simp [queryCount]
  | query q next ih =>
    simp only [queryCount]
    have := ih (oracle q)
    omega

theorem transcriptQueryCount_le (replies : ℕ → Q → R) (round : ℕ)
    {k : ℕ} (p : QueryProgram Q R O k) :
    p.transcriptQueryCount replies round ≤ k := by
  induction p generalizing round with
  | pure output => simp [transcriptQueryCount]
  | query q next ih =>
    simp only [transcriptQueryCount]
    have := ih (replies round q) (round + 1)
    omega

/-- Compile each target query to two sequential source queries. The second
source query may depend on the first reply. -/
def compileTwo (first : Q → Q') (second : Q → R' → Q')
    (combine : Q → R' → R' → R) :
    {k : ℕ} → QueryProgram Q R O k → QueryProgram Q' R' O (2 * k)
  | _, .pure output => .pure output
  | _, .query q next => .query (first q) (fun r₁ =>
      .query (second q r₁) (fun r₂ => compileTwo first second combine (next (combine q r₁ r₂))))

theorem compileTwo_eval (first : Q → Q') (second : Q → R' → Q')
    (combine : Q → R' → R' → R) (source : Q' → R') (target : Q → R)
    (hsim : ∀ q, combine q (source (first q)) (source (second q (source (first q)))) = target q)
    {k : ℕ} (p : QueryProgram Q R O k) :
    (p.compileTwo first second combine).eval source = p.eval target := by
  induction p with
  | pure output => rfl
  | query q next ih =>
    simp only [compileTwo, eval, hsim]
    exact ih (target q)

/-- Exact accounting along matching executions, including early stopping. -/
theorem compileTwo_queryCount (first : Q → Q') (second : Q → R' → Q')
    (combine : Q → R' → R' → R) (source : Q' → R') (target : Q → R)
    (hsim : ∀ q, combine q (source (first q)) (source (second q (source (first q)))) = target q)
    {k : ℕ} (p : QueryProgram Q R O k) :
    (p.compileTwo first second combine).queryCount source = 2 * p.queryCount target := by
  induction p with
  | pure output => simp [compileTwo, queryCount]
  | query q next ih =>
    simp only [compileTwo, queryCount, hsim, ih]
    omega

/-- The cap holds for every source oracle, without a compatibility or promise
assumption; thus it also holds on inadmissible matrix transcripts. -/
theorem compileTwo_hard_cap (first : Q → Q') (second : Q → R' → Q')
    (combine : Q → R' → R' → R) (source : Q' → R')
    {k : ℕ} (p : QueryProgram Q R O k) :
    (p.compileTwo first second combine).queryCount source ≤ 2 * k :=
  queryCount_le _ _

theorem compileTwo_all_transcripts (first : Q → Q') (second : Q → R' → Q')
    (combine : Q → R' → R' → R) (replies : ℕ → Q' → R') (round : ℕ)
    {k : ℕ} (p : QueryProgram Q R O k) :
    (p.compileTwo first second combine).transcriptQueryCount replies round ≤ 2 * k :=
  transcriptQueryCount_le _ _ _

end QueryProgram

noncomputable section
open Matrix
open scoped Matrix

variable {d n m : Type*} [Fintype d] [Fintype n] [Fintype m]

/-- One exact two-sided matvec query. -/
def matrixOracle (A : Matrix m n ℝ) (q : (n → ℝ) × (m → ℝ)) :
    (m → ℝ) × (n → ℝ) := (A *ᵥ q.1, A.transpose *ᵥ q.2)

def simplexCombine (b : d → ℝ) (R : Matrix d m ℝ) (V : Matrix d n ℝ)
    (Λ : ℝ) (q : (n → ℝ) × (m → ℝ)) (h₁ h₂ : d → ℝ) :
    (m → ℝ) × (n → ℝ) :=
  (Λ⁻¹ • (R.transpose *ᵥ (h₁ - (∑ j, q.1 j) • b)),
    Λ⁻¹ • (V.transpose *ᵥ h₂ - fun _ => dotProduct b (R *ᵥ q.2)))

theorem simplexCombine_correct (H : Matrix d d ℝ) (hH : H.transpose = H)
    (b : d → ℝ) (R : Matrix d m ℝ) (V : Matrix d n ℝ) (Λ : ℝ)
    (q : (n → ℝ) × (m → ℝ)) :
    simplexCombine b R V Λ q (H *ᵥ (V *ᵥ q.1)) (H *ᵥ (R *ᵥ q.2)) =
      matrixOracle (simplexMatrix H b R V Λ) q := by
  rw [matrixOracle, simplexMatrix_mulVec, simplexMatrix_transpose_mulVec H b hH]
  rfl

/-- The simplex game's entire adaptive execution, compiled using only access
to the source matvec oracle. The compiler does not inspect H. -/
def compileSimplex {O : Type*} {k : ℕ} (b : d → ℝ)
    (R : Matrix d m ℝ) (V : Matrix d n ℝ) (Λ : ℝ)
    (p : QueryProgram ((n → ℝ) × (m → ℝ)) ((m → ℝ) × (n → ℝ)) O k) :
    QueryProgram (d → ℝ) (d → ℝ) O (2 * k) :=
  p.compileTwo (fun q => V *ᵥ q.1) (fun q _ => R *ᵥ q.2) (simplexCombine b R V Λ)

theorem compileSimplex_eval {O : Type*} {k : ℕ} (H : Matrix d d ℝ)
    (hH : H.transpose = H) (b : d → ℝ)
    (R : Matrix d m ℝ) (V : Matrix d n ℝ) (Λ : ℝ)
    (p : QueryProgram ((n → ℝ) × (m → ℝ)) ((m → ℝ) × (n → ℝ)) O k) :
    (compileSimplex b R V Λ p).eval H.mulVec =
      p.eval (matrixOracle (simplexMatrix H b R V Λ)) := by
  apply QueryProgram.compileTwo_eval
  exact simplexCombine_correct H hH b R V Λ

theorem compileSimplex_hard_cap {O : Type*} {k : ℕ} (b : d → ℝ)
    (R : Matrix d m ℝ) (V : Matrix d n ℝ) (Λ : ℝ)
    (p : QueryProgram ((n → ℝ) × (m → ℝ)) ((m → ℝ) × (n → ℝ)) O k)
    (source : (d → ℝ) → (d → ℝ)) :
    (compileSimplex b R V Λ p).queryCount source ≤ 2 * k :=
  QueryProgram.queryCount_le _ _

/-- Randomized programs are compiled with the same seed. Therefore every
success event is literally unchanged on each fixed source matrix. -/
theorem compileSimplex_success_event {Seed O : Type*} {k : ℕ} (H : Matrix d d ℝ)
    (hH : H.transpose = H) (b : d → ℝ)
    (R : Matrix d m ℝ) (V : Matrix d n ℝ) (Λ : ℝ)
    (p : Seed → QueryProgram ((n → ℝ) × (m → ℝ)) ((m → ℝ) × (n → ℝ)) O k)
    (success : O → Prop) :
    {seed | success ((compileSimplex b R V Λ (p seed)).eval H.mulVec)} =
      {seed | success ((p seed).eval (matrixOracle (simplexMatrix H b R V Λ)))} := by
  ext seed
  simp only [Set.mem_setOf_eq, compileSimplex_eval H hH]

def ballCombine (b : d → ℝ) (α β : ℝ)
    (q : ((d ⊕ Unit) → ℝ) × ((d ⊕ d) → ℝ)) (h₁ h₂ : d → ℝ) :
    ((d ⊕ d) → ℝ) × ((d ⊕ Unit) → ℝ) :=
  let s := q.1 (Sum.inr ())
  let yp : d → ℝ := fun i => q.2 (Sum.inl i)
  let ym : d → ℝ := fun i => q.2 (Sum.inr i)
  (-Sum.elim (fun i => α * s + β * (h₁ i - s * b i))
      (fun i => α * s - β * (h₁ i - s * b i)),
    -Sum.elim (β • h₂)
      (fun _ => α * ((∑ i, yp i) + ∑ i, ym i) - β * dotProduct b (yp - ym)))

theorem ballCombine_correct (H : Matrix d d ℝ) (hH : H.transpose = H)
    (b : d → ℝ) (α β : ℝ)
    (q : ((d ⊕ Unit) → ℝ) × ((d ⊕ d) → ℝ)) :
    ballCombine b α β q
      (H *ᵥ (fun i => q.1 (Sum.inl i)))
      (H *ᵥ ((fun i => q.2 (Sum.inl i)) - (fun i => q.2 (Sum.inr i)))) =
      matrixOracle (-ballMatrix H b α β) q := by
  have hw : q.1 = Sum.elim (fun i => q.1 (Sum.inl i)) (fun _ : Unit => q.1 (Sum.inr ())) := by
    ext i
    cases i with
    | inl i => rfl
    | inr i => cases i; rfl
  have hy : q.2 = Sum.elim (fun i => q.2 (Sum.inl i)) (fun i => q.2 (Sum.inr i)) := by
    ext i
    cases i <;> rfl
  unfold matrixOracle
  rw [Matrix.neg_mulVec, Matrix.transpose_neg, Matrix.neg_mulVec]
  conv_rhs =>
    lhs
    rw [hw, ballMatrix_mulVec]
  conv_rhs =>
    rhs
    rw [hy, ballMatrix_transpose_mulVec H b hH]
  rfl

/-- Compiler for the actual ball-simplex payoff matrix A = -C. -/
def compileBall {O : Type*} {k : ℕ} (b : d → ℝ) (α β : ℝ)
    (p : QueryProgram (((d ⊕ Unit) → ℝ) × ((d ⊕ d) → ℝ))
      (((d ⊕ d) → ℝ) × ((d ⊕ Unit) → ℝ)) O k) :
    QueryProgram (d → ℝ) (d → ℝ) O (2 * k) :=
  p.compileTwo (fun q i => q.1 (Sum.inl i))
    (fun q _ => (fun i => q.2 (Sum.inl i)) - (fun i => q.2 (Sum.inr i)))
    (ballCombine b α β)

theorem compileBall_eval {O : Type*} {k : ℕ} (H : Matrix d d ℝ)
    (hH : H.transpose = H) (b : d → ℝ) (α β : ℝ)
    (p : QueryProgram (((d ⊕ Unit) → ℝ) × ((d ⊕ d) → ℝ))
      (((d ⊕ d) → ℝ) × ((d ⊕ Unit) → ℝ)) O k) :
    (compileBall b α β p).eval H.mulVec =
      p.eval (matrixOracle (-ballMatrix H b α β)) := by
  apply QueryProgram.compileTwo_eval
  exact ballCombine_correct H hH b α β

theorem compileBall_hard_cap {O : Type*} {k : ℕ} (b : d → ℝ) (α β : ℝ)
    (p : QueryProgram (((d ⊕ Unit) → ℝ) × ((d ⊕ d) → ℝ))
      (((d ⊕ d) → ℝ) × ((d ⊕ Unit) → ℝ)) O k)
    (source : (d → ℝ) → (d → ℝ)) :
    (compileBall b α β p).queryCount source ≤ 2 * k :=
  QueryProgram.queryCount_le _ _

theorem compileBall_success_event {Seed O : Type*} {k : ℕ} (H : Matrix d d ℝ)
    (hH : H.transpose = H) (b : d → ℝ) (α β : ℝ)
    (p : Seed → QueryProgram (((d ⊕ Unit) → ℝ) × ((d ⊕ d) → ℝ))
      (((d ⊕ d) → ℝ) × ((d ⊕ Unit) → ℝ)) O k) (success : O → Prop) :
    {seed | success ((compileBall b α β (p seed)).eval H.mulVec)} =
      {seed | success ((p seed).eval (matrixOracle (-ballMatrix H b α β)))} := by
  ext seed
  simp only [Set.mem_setOf_eq, compileBall_eval H hH]

end
end Matvec
