import VIReference.Pilot.Oracle

/-!
# Exact-oracle execution and padding semantics

This module connects a Borel stopping policy to the unknown operator that it
actually queries.  An unpadded run contains exactly the calls made before the
first `stop`; a padded run is only a fixed-length transcript representation of
the same stopped run and retains the saved output.
-/

open Set MeasureTheory

namespace VIReference.Pilot

section ExactOracle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- An actual order-`p` oracle for `F`: every component of every returned
symmetric jet is the corresponding iterated Fréchet derivative of `F`.

The symmetry proof is carried by `SymmetricExactJet`; `exact` prevents a
policy execution from being coupled to arbitrary values of that ambient type.
-/
structure ExactSymmetricJetOracle (data : VIPublicData E) (F : E → E) where
  answer : E → SymmetricExactJet E data.p
  exact : ∀ x (j : Fin data.p),
    ((answer x) j).1 = iteratedFDeriv ℝ j.1 F x

/-- Build the actual exact oracle once arbitrary-order derivative symmetry has
been supplied.  This witness is explicit because mathlib does not currently
bundle the required all-orders symmetry theorem in the exact-jet type. -/
noncomputable def ExactSymmetricJetOracle.ofSymmetricDerivatives
    (data : VIPublicData E) (F : E → E)
    (hSymm : ∀ x (j : Fin data.p) (σ : Equiv.Perm (Fin j.1)),
      ContinuousMultilinearMap.domDomCongr σ
        (iteratedFDeriv ℝ j.1 F x) = iteratedFDeriv ℝ j.1 F x) :
    ExactSymmetricJetOracle data F where
  answer x := exactSymmetricJetOf E data.p F x (hSymm x)
  exact _ _ := rfl

end ExactOracle

namespace OracleHistory

variable {E Answer : Type*} {X : Set E}

/-- Restrict a transcript of length `m` to its first `n ≤ m` entries. -/
def restrict {m n : ℕ} (history : OracleHistory X Answer m) (hn : n ≤ m) :
    OracleHistory X Answer n :=
  fun i => history ⟨i.1, lt_of_lt_of_le i.2 hn⟩

/-- Extend a transcript to a larger fixed length using one ignored feasible
query/answer pair.  This is a representation operation, not an oracle call
performed by the unpadded policy. -/
def pad {m n : ℕ} (history : OracleHistory X Answer n) (_hn : n ≤ m)
    (fill : X × Answer) : OracleHistory X Answer m :=
  fun i => if hi : i.1 < n then history ⟨i.1, hi⟩ else fill

@[simp] theorem restrict_pad {m n : ℕ} (history : OracleHistory X Answer n)
    (hn : n ≤ m) (fill : X × Answer) :
    restrict (pad history hn fill) hn = history := by
  funext i
  simp [restrict, pad, i.2]

end OracleHistory

section Runs

variable {E Answer : Type*} [MeasurableSpace E] [MeasurableSpace Answer]

/-- A genuine early-stopped run with exactly `n` oracle calls.

For every proper prefix the policy asks for the next recorded feasible point,
and the recorded answer is the actual oracle answer.  At the full history the
policy returns `output`; no rule after that stop is evaluated. -/
def BorelStoppingPolicy.IsUnpaddedRun {X : Set E} {budget : ℕ}
    (policy : BorelStoppingPolicy (Answer := Answer) X budget)
    (oracle : E → Answer) (seed : policy.Seed) (n : ℕ) (hn : n ≤ budget)
    (history : OracleHistory X Answer n) (output : X) : Prop :=
  (∀ i : Fin n,
    policy.rule
        ⟨i.1, Nat.lt_trans (Nat.lt_of_lt_of_le i.2 hn)
          (Nat.lt_succ_self budget)⟩
        (seed, OracleHistory.restrict history (Nat.le_of_lt i.2)) =
          Sum.inr (history i).1 ∧
    (history i).2 = oracle (history i).1) ∧
  policy.rule ⟨n, Nat.lt_succ_of_le hn⟩ (seed, history) = Sum.inl output

/-- The paper's fixed-length padded normal form.  There is a genuine stopped
prefix with the saved output, while the remaining feasible entries are ignored
and merely filled with exact oracle answers up to the worst-case cap. -/
def BorelStoppingPolicy.IsPaddedRun {X : Set E} {budget : ℕ}
    (policy : BorelStoppingPolicy (Answer := Answer) X budget)
    (oracle : E → Answer) (seed : policy.Seed)
    (history : OracleHistory X Answer budget) (output : X) : Prop :=
  (∀ i : Fin budget, (history i).2 = oracle (history i).1) ∧
  ∃ n, ∃ hn : n ≤ budget,
    policy.IsUnpaddedRun oracle seed n hn
      (OracleHistory.restrict history hn) output

/-- Padding is semantically inert: existence of a genuine early-stopped run is
equivalent to existence of a fixed-cap padded transcript with the same saved
output.  The forward construction only extends data; it performs no additional
calls in `IsUnpaddedRun`. -/
theorem BorelStoppingPolicy.unpadded_iff_padded {X : Set E} {budget : ℕ}
    (policy : BorelStoppingPolicy (Answer := Answer) X budget)
    (oracle : E → Answer) (seed : policy.Seed) (fill : X) (output : X) :
    (∃ n, ∃ hn : n ≤ budget, ∃ history : OracleHistory X Answer n,
      policy.IsUnpaddedRun oracle seed n hn history output) ↔
    (∃ history : OracleHistory X Answer budget,
      policy.IsPaddedRun oracle seed history output) := by
  constructor
  · rintro ⟨n, hn, history, hrun⟩
    let padded : OracleHistory X Answer budget :=
      OracleHistory.pad history hn (fill, oracle fill.1)
    refine ⟨padded, ?_, n, hn, ?_⟩
    · intro i
      by_cases hi : i.1 < n
      · have hexact := (hrun.1 ⟨i.1, hi⟩).2
        simpa [padded, OracleHistory.pad, hi] using hexact
      · simp [padded, OracleHistory.pad, hi]
    · simpa [padded] using hrun
  · rintro ⟨history, _hexact, n, hn, hrun⟩
    exact ⟨n, hn, OracleHistory.restrict history hn, hrun⟩

end Runs

section Success

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A concrete stopped run succeeds on `F` exactly when its saved feasible
output has tangent residual at most `epsilon`.  This defines the success event;
it does not incorrectly assert that every admitted algorithm succeeds. -/
def BorelStoppingPolicy.RunSucceedsOn (data : VIPublicData E) (F : E → E)
    (epsilon : ℝ)
    (policy : BorelStoppingPolicy (Answer := SymmetricExactJet E data.p)
      data.X budget)
    (oracle : ExactSymmetricJetOracle data F) (seed : policy.Seed)
    (n : ℕ) (hn : n ≤ budget)
    (history : OracleHistory data.X (SymmetricExactJet E data.p) n)
    (output : data.X) : Prop :=
  policy.IsUnpaddedRun oracle.answer seed n hn history output ∧
    tangentResidual data F output.1 ≤ epsilon

end Success

end VIReference.Pilot
