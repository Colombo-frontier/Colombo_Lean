import VIReference.Pilot.Model

/-!
# Symmetric exact jets and measurable early-stopping oracle policies

This module closes two semantic gaps in the first pilot model:

* the oracle answer records that every higher derivative is symmetric under
  arbitrary permutations of its arguments;
* an action is either `stop output` or `query point`, so stopping consumes no
  padded oracle call.  The history length is exactly the number of completed
  queries and the rule at the cap is required to stop.
-/

open Set MeasureTheory

namespace VIReference.Pilot

section SymmetricJet

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A continuous multilinear map is symmetric when permuting all input slots
does not change it.  This includes the arity-zero case. -/
def IsSymmetricContinuousMultilinearMap {n : ℕ}
    (f : E [×n]→L[ℝ] E) : Prop :=
  ∀ σ : Equiv.Perm (Fin n), ContinuousMultilinearMap.domDomCongr σ f = f

/-- The symmetric subspace used by the article's ambient exact-jet oracle. -/
abbrev SymmetricContinuousMultilinearMap (n : ℕ) :=
  {f : E [×n]→L[ℝ] E // IsSymmetricContinuousMultilinearMap E f}

/-- The full order-`p` jet `(F, DF, ..., D^(p-1)F)`, with symmetry carried in
the type rather than left as a prose side condition. -/
abbrev SymmetricExactJet (p : ℕ) :=
  (j : Fin p) → SymmetricContinuousMultilinearMap E j.1

/-- Package the actual iterated derivatives once their permutation symmetry
has been proved.  Mathlib currently supplies convenient second-derivative
symmetry results, but not the arbitrary-order bundled theorem needed here. -/
noncomputable def exactSymmetricJetOf (p : ℕ) (F : E → E) (x : E)
    (hSymm : ∀ (j : Fin p) (σ : Equiv.Perm (Fin j.1)),
      ContinuousMultilinearMap.domDomCongr σ
        (iteratedFDeriv ℝ j.1 F x) = iteratedFDeriv ℝ j.1 F x) :
    SymmetricExactJet E p :=
  fun j => ⟨iteratedFDeriv ℝ j.1 F x, hSymm j⟩

end SymmetricJet

section MeasurableSymmetricJet

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Canonical norm-Borel measurable structure on continuous multilinear maps.
This is project glue missing from mathlib's current instance graph. -/
noncomputable instance cmlmMeasurableSpace (n : ℕ) :
    MeasurableSpace (E [×n]→L[ℝ] E) := borel (E [×n]→L[ℝ] E)

instance cmlmBorelSpace (n : ℕ) : BorelSpace (E [×n]→L[ℝ] E) := ⟨rfl⟩

/-- The symmetric tensor subtype carries the induced measurable structure.
Because the ambient tensor space is Borel, this is also exactly the Borel
structure of the subtype topology. -/
noncomputable instance symmetricCMLMMeasurableSpace (n : ℕ) :
    MeasurableSpace (SymmetricContinuousMultilinearMap E n) :=
  @Subtype.instMeasurableSpace (E [×n]→L[ℝ] E)
    (IsSymmetricContinuousMultilinearMap E) (cmlmMeasurableSpace E n)

instance symmetricCMLMBorelSpace (n : ℕ) :
    BorelSpace (SymmetricContinuousMultilinearMap E n) :=
  Subtype.borelSpace (IsSymmetricContinuousMultilinearMap E)

end MeasurableSymmetricJet

section EarlyStopping

variable {E Answer : Type*} [MeasurableSpace E] [MeasurableSpace Answer]

/-- `inl output` stops without another oracle call; `inr query` performs one
oracle call.  Both payloads have subtype `X`, hence are feasible. -/
abbrev OracleAction (X : Set E) := Sum X X

/-- A Borel policy with a hard query cap and genuine early stopping.

At a history of length `n`, the policy has made exactly `n` oracle calls.  Its
next measurable action may stop or query.  At history length `budget` it must
stop, so no execution can exceed the cap and no padding query is introduced.
The seed/law and all rules are fixed without mentioning the unknown operator.
-/
structure BorelStoppingPolicy (X : Set E) (budget : ℕ) where
  Seed : Type*
  seedMeasurable : MeasurableSpace Seed
  seedMeasure : @Measure Seed seedMeasurable
  seedProbability : @IsProbabilityMeasure Seed seedMeasurable seedMeasure
  rule : (n : Fin (budget + 1)) →
    Seed × OracleHistory X Answer n.1 → OracleAction X
  rule_measurable : ∀ n, @Measurable
    (Seed × OracleHistory X Answer n.1) (OracleAction X)
    (MeasurableSpace.prod seedMeasurable inferInstance) inferInstance
    (rule n)
  cap_stops : ∀ state : Seed × OracleHistory X Answer budget,
    ∃ output : X, rule ⟨budget, Nat.lt_add_one budget⟩ state = Sum.inl output

/-- Deterministic policies use a genuinely singleton seed space: inhabited and
subsingleton.  `Subsingleton` alone would incorrectly admit the empty type. -/
def BorelStoppingPolicy.IsDeterministic {X : Set E} {budget : ℕ}
    (policy : BorelStoppingPolicy (Answer := Answer) X budget) : Prop :=
  Nonempty policy.Seed ∧ Subsingleton policy.Seed

end EarlyStopping

end VIReference.Pilot
