import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Branch accounting and the terminal scalar contradiction

This file formalizes the combinatorial accounting core of Appendix E.2--E.3
and the final scalar argument of Theorem E.19 of arXiv:2610.16991v2.

`MassProfile` records the actual invariants needed of normalized reachable word
counts: nonnegativity, the unit upper bound, and deletion monotonicity.  The
finite-set lemmas below prove the one-layer counting facts behind this interface.
`AccountingRun` then allows arbitrary interleavings of simultaneous matrix
updates and legal prefix resets.  Its bound is proved by induction on the entire
chronology, rather than by assuming a separate bound for each stage.

The terminal scalar theorem assumes the two projected connector equations and
the numerical bounds established analytically in the manuscript.  It proves
their contradiction; it does not assume or assert those analytic bounds for the
paper's functions.  No Haar law, oracle simulation, Moreau theorem, or randomized
optimization lower bound is asserted in this file.
-/

namespace NCConcave16991
namespace BranchAccounting

/-- Deleting the first letter gives at most one fiber of size `card α` over
each permitted suffix.  This is the counting content of Lemma E.2. -/
theorem deletion_closed_card_bound {α β : Type*} [Fintype α]
    [DecidableEq α] [DecidableEq β]
    (upper : Finset (α × β)) (lower : Finset β)
    (hdelete : ∀ w ∈ upper, w.2 ∈ lower) :
    upper.card ≤ Fintype.card α * lower.card := by
  calc
    upper.card ≤ (Finset.univ.product lower).card :=
      Finset.card_le_card (by
        intro w hw
        exact Finset.mem_product.mpr ⟨Finset.mem_univ _, hdelete w hw⟩)
    _ = Fintype.card α * lower.card := by simp

/-- After normalizing word counts, deletion closure makes reachable mass
nonincreasing with depth. -/
theorem deletion_closed_normalized_mass {β : Type*} [DecidableEq β]
    (n t : ℕ) (hn : 0 < n)
    (upper : Finset (Fin n × β)) (lower : Finset β)
    (hdelete : ∀ w ∈ upper, w.2 ∈ lower) :
    (upper.card : ℝ) / (n : ℝ) ^ (t + 1) ≤
      (lower.card : ℝ) / (n : ℝ) ^ t := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hcardNat : upper.card ≤ n * lower.card := by
    simpa using deletion_closed_card_bound upper lower hdelete
  have hcard : (upper.card : ℝ) ≤ (n : ℝ) * lower.card := by
    exact_mod_cast hcardNat
  apply (div_le_div_iff₀ (pow_pos hnR _) (pow_pos hnR _)).mpr
  calc
    (upper.card : ℝ) * (n : ℝ) ^ t ≤
        ((n : ℝ) * lower.card) * (n : ℝ) ^ t :=
      mul_le_mul_of_nonneg_right hcard (pow_nonneg hnR.le _)
    _ = (lower.card : ℝ) * (n : ℝ) ^ (t + 1) := by ring

/-- A simultaneous update prepends one selected letter to old lower words.
Duplicates can only reduce the increase. -/
theorem simultaneous_update_card_bound {α β : Type*}
    [DecidableEq α] [DecidableEq β]
    (upper : Finset (α × β)) (lower : Finset β) (i : α) :
    (upper ∪ lower.image (fun w => (i, w))).card ≤
      upper.card + lower.card := by
  calc
    (upper ∪ lower.image (fun w => (i, w))).card ≤
        upper.card + (lower.image (fun w => (i, w))).card :=
      Finset.card_union_le _ _
    _ ≤ upper.card + lower.card :=
      Nat.add_le_add_left (Finset.card_image_le) _

/-- The normalized reachable masses and their deletion-closure invariants. -/
structure MassProfile where
  mass : ℕ → ℝ
  nonneg : ∀ t, 0 ≤ mass t
  le_one : ∀ t, mass t ≤ 1
  antitone : Antitone mass

instance : CoeFun MassProfile (fun _ => ℕ → ℝ) := ⟨MassProfile.mass⟩

/-- Initially only the empty word at the root is reachable. -/
def rootMass : MassProfile where
  mass t := if t = 0 then 1 else 0
  nonneg t := by split_ifs <;> norm_num
  le_one t := by split_ifs <;> norm_num
  antitone := by
    intro a b hab
    by_cases hb : b = 0
    · have ha : a = 0 := Nat.eq_zero_of_le_zero (hb ▸ hab)
      simp [ha, hb]
    · simp only [hb, ↓reduceIte]
      split_ifs <;> norm_num

/-- Revealing source `j` fills the prefix through `j`. -/
def prefixReset (p : MassProfile) (j : ℕ) : MassProfile where
  mass t := if t ≤ j then 1 else p t
  nonneg t := by
    split_ifs
    · norm_num
    · exact p.nonneg t
  le_one t := by
    split_ifs
    · exact le_rfl
    · exact p.le_one t
  antitone := by
    intro a b hab
    by_cases hb : b ≤ j
    · have ha := hab.trans hb
      simp [ha, hb]
    · by_cases ha : a ≤ j
      · simpa [ha, hb] using p.le_one b
      · simpa [ha, hb] using p.antitone hab

/-- A legal reset increases every coordinate by at most `ρ⁻¹`.
This proves the amplification conclusion of E.2 from eligibility and deletion
monotonicity, rather than taking amplification as an assumption. -/
theorem prefixReset_le_div (p : MassProfile) (j : ℕ) (ρ : ℝ)
    (hρ : 0 < ρ) (hρone : ρ ≤ 1) (heligible : ρ ≤ p j) (t : ℕ) :
    prefixReset p j t ≤ p t / ρ := by
  change (if t ≤ j then 1 else p t) ≤ p t / ρ
  split_ifs with ht
  · apply (le_div_iff₀ hρ).mpr
    simpa using heligible.trans (p.antitone ht)
  · apply (le_div_iff₀ hρ).mpr
    nlinarith [p.nonneg t]

/-- The binomial propagation bound before truncating it at one. -/
noncomputable def accountingBound (n ρ : ℝ) (k r t : ℕ) : ℝ :=
  (Nat.choose k t : ℝ) / (n ^ t * ρ ^ r)

theorem accountingBound_pascal (n ρ : ℝ) (hn : 0 < n) (hρ : 0 < ρ)
    (k r t : ℕ) :
    accountingBound n ρ k r (t + 1) + accountingBound n ρ k r t / n =
      accountingBound n ρ (k + 1) r (t + 1) := by
  unfold accountingBound
  rw [Nat.choose_succ_succ']
  push_cast
  rw [pow_succ]
  field_simp [ne_of_gt hn, ne_of_gt hρ]
  ring

theorem accountingBound_reset (n ρ : ℝ) (k r t : ℕ) :
    accountingBound n ρ k r t / ρ = accountingBound n ρ k (r + 1) t := by
  unfold accountingBound
  rw [pow_succ, div_div]
  congr 1
  ring

/-- A complete chronology.  Each matrix round uses old lower-layer masses,
as required by the simultaneous update.  Source releases may occur after any
round and in any legal order; neither indices nor release choices are assumed
independent of the history. -/
inductive AccountingRun (n ρ : ℝ) : ℕ → ℕ → MassProfile → Prop
  | initial : AccountingRun n ρ 0 0 rootMass
  | matrix {k r : ℕ} {p : MassProfile}
      (prior : AccountingRun n ρ k r p) (q : MassProfile)
      (root : q 0 ≤ p 0)
      (step : ∀ t, q (t + 1) ≤ p (t + 1) + p t / n) :
      AccountingRun n ρ (k + 1) r q
  | release {k r : ℕ} {p : MassProfile}
      (prior : AccountingRun n ρ k r p) (j : ℕ)
      (eligible : ρ ≤ p j) :
      AccountingRun n ρ k (r + 1) (prefixReset p j)

/-- E.3's chronological binomial estimate for every admissible abstract run.
The conclusion is a theorem of the update/reset rules, including arbitrary
cached lower-layer mass; no stagewise product assumption occurs. -/
theorem chronological_bound {n ρ : ℝ}
    (hn : 0 < n) (hρ : 0 < ρ) (hρone : ρ ≤ 1)
    {k r : ℕ} {p : MassProfile} (run : AccountingRun n ρ k r p) :
    ∀ t, p t ≤ accountingBound n ρ k r t := by
  induction run with
  | initial =>
    intro t
    cases t with
    | zero => simp [rootMass, accountingBound]
    | succ t => simp [rootMass, accountingBound]
  | @matrix k r p prior q hroot hstep ih =>
    intro t
    cases t with
    | zero =>
      calc
        q 0 ≤ p 0 := hroot
        _ ≤ accountingBound n ρ k r 0 := ih 0
        _ = accountingBound n ρ (k + 1) r 0 := by simp [accountingBound]
    | succ t =>
      calc
        q (t + 1) ≤ p (t + 1) + p t / n := hstep t
        _ ≤ accountingBound n ρ k r (t + 1) +
            accountingBound n ρ k r t / n :=
          add_le_add (ih (t + 1)) (div_le_div_of_nonneg_right (ih t) hn.le)
        _ = accountingBound n ρ (k + 1) r (t + 1) :=
          accountingBound_pascal n ρ hn hρ k r t
  | @release k r p prior j heligible ih =>
    intro t
    calc
      prefixReset p j t ≤ p t / ρ :=
        prefixReset_le_div p j ρ hρ hρone heligible t
      _ ≤ accountingBound n ρ k r t / ρ :=
        div_le_div_of_nonneg_right (ih t) hρ.le
      _ = accountingBound n ρ k (r + 1) t :=
        accountingBound_reset n ρ k r t

/-- The precise clipped form of equation (73). -/
theorem chronological_bound_clipped {n ρ : ℝ}
    (hn : 0 < n) (hρ : 0 < ρ) (hρone : ρ ≤ 1)
    {k r : ℕ} {p : MassProfile} (run : AccountingRun n ρ k r p) (t : ℕ) :
    p t ≤ min 1 (accountingBound n ρ k r t) :=
  le_min (p.le_one t) (chronological_bound hn hρ hρone run t)

/-- A source beyond the number of completed matrix rounds remains unreachable,
even after legal prefix releases. -/
theorem mass_eq_zero_of_rounds_lt_depth {n ρ : ℝ}
    (hn : 0 < n) (hρ : 0 < ρ) (hρone : ρ ≤ 1)
    {k r : ℕ} {p : MassProfile} (run : AccountingRun n ρ k r p)
    (t : ℕ) (hkt : k < t) : p t = 0 := by
  have hb := chronological_bound hn hρ hρone run t
  have hc : Nat.choose k t = 0 := Nat.choose_eq_zero_of_lt hkt
  simp [accountingBound, hc] at hb
  exact le_antisymm hb (p.nonneg t)

/-- Solving E.19's two projected connector equations, with their actual error
bounds, forces the exit connector above `73/60`. -/
theorem frontier_exit_scalar_lower_bound (A B s ga gb : ℝ)
    (hs : -(1 / 10 : ℝ) < s)
    (hga : |ga| ≤ (1 / 20 : ℝ)) (hgb : |gb| ≤ (1 / 20 : ℝ))
    (ha : ga = 2 * A - B - 4) (hb : gb = -A + 2 * B - s) :
    (73 / 60 : ℝ) < B := by
  have hga_lower := (abs_le.mp hga).1
  have hgb_lower := (abs_le.mp hgb).1
  linarith

/-- The final scalar contradiction of Theorem E.19.  Its hypotheses state the
analytic interface explicitly: the two projected connector equations, the low
score bound, the low-state penalty derivative bound, and the three projected
small-gradient bounds.  This theorem proves their incompatibility. -/
theorem terminal_scalar_contradiction (A B s ga gb D : ℝ)
    (hs : -(1 / 10 : ℝ) < s)
    (hga : |ga| ≤ (1 / 20 : ℝ)) (hgb : |gb| ≤ (1 / 20 : ℝ))
    (ha : ga = 2 * A - B - 4) (hb : gb = -A + 2 * B - s)
    (hD : D ≤ (1 / 50 : ℝ)) (hstate : |D - B| ≤ (1 / 20 : ℝ)) : False := by
  have hB := frontier_exit_scalar_lower_bound A B s ga gb hs hga hgb ha hb
  have hstate_lower := (abs_le.mp hstate).1
  linarith

end BranchAccounting
end NCConcave16991
