import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Count
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Balanced replication: deterministic kernel of Appendix F.2

The public partition here is the actual residue partition `i ↦ i % s` of the
component indices `0,…,n-1`. Its group sizes are computed from Euclidean
division, rather than assumed. Positive weights bounded by two are proved, and
the vector-valued average identity is obtained by summing over those fibers.

The oracle simulation and transcript results are deterministic and pointwise in
every adaptive policy (and hence in every fixed private random seed). They do
not assert the separate Moreau-parameter transfer or an oracle lower bound.
-/

namespace NCConcave16991
namespace Replication

open scoped BigOperators

/-- The public residue group of source component `j`. -/
def group (n s j : ℕ) : Finset ℕ :=
  (Finset.range n).filter (fun i => i % s = j)

def groupSize (n s j : ℕ) : ℕ := (group n s j).card

theorem count_mod_small (s r j : ℕ) (hr : r ≤ s) :
    Nat.count (fun i => i % s = j) r = if j < r then 1 else 0 := by
  rw [Nat.count_eq_card_filter_range]
  have hset : (Finset.range r).filter (fun i => i % s = j) =
      (Finset.range r).filter (fun i => i = j) := by
    apply Finset.filter_congr
    intro i hi
    rw [Nat.mod_eq_of_lt ((Finset.mem_range.mp hi).trans_le hr)]
  rw [hset]
  simp only [Finset.filter_eq', Finset.mem_range]
  split_ifs <;> simp

theorem count_mod_blocks (s q r j : ℕ) (hr : r < s) (hj : j < s) :
    Nat.count (fun i => i % s = j) (s * q + r) =
      q + if j < r then 1 else 0 := by
  induction q with
  | zero => simpa using count_mod_small s r j hr.le
  | succ q ih =>
    have hlen : s * (q + 1) + r = s + (s * q + r) := by ring
    rw [hlen, Nat.count_add]
    have hp : (fun k => (s + k) % s = j) = (fun k => k % s = j) := by
      funext k
      simp
    simp only [hp]
    simp only [count_mod_small s s j le_rfl, hj, ↓reduceIte, ih]
    omega

/-- Exact floor/remainder formula for the actual residue groups. -/
theorem groupSize_eq (n s j : ℕ) (hs : 0 < s) (hj : j < s) :
    groupSize n s j = n / s + if j < n % s then 1 else 0 := by
  have hcount : groupSize n s j = Nat.count (fun i => i % s = j) n := by
    simp [groupSize, group, Nat.count_eq_card_filter_range]
  rw [hcount]
  have hn : s * (n / s) + n % s = n := by
    simpa [Nat.add_comm] using Nat.mod_add_div n s
  conv_lhs => rw [← hn]
  exact count_mod_blocks s (n / s) (n % s) j (Nat.mod_lt n hs) hj

theorem groupSize_bounds (n s j : ℕ) (hs : 0 < s) (hj : j < s) :
    n / s ≤ groupSize n s j ∧ groupSize n s j ≤ n / s + 1 := by
  rw [groupSize_eq n s j hs hj]
  split_ifs <;> omega

theorem groupSize_pos (n s j : ℕ) (hs : 0 < s) (hsn : s ≤ n) (hj : j < s) :
    0 < groupSize n s j :=
  lt_of_lt_of_le (Nat.div_pos hsn hs) (groupSize_bounds n s j hs hj).1

/-- Every source component has a nonempty public group. -/
theorem residue_group_surjective (n s : ℕ) (_hs : 0 < s) (hsn : s ≤ n)
    (j : ℕ) (hj : j < s) : ∃ i < n, i % s = j := by
  exact ⟨j, hj.trans_le hsn, Nat.mod_eq_of_lt hj⟩

noncomputable def weight (n s j : ℕ) : ℝ :=
  (n : ℝ) / ((s : ℝ) * groupSize n s j)

/-- The reserved factor of two in individual smoothness suffices for all
unequal residue-group sizes. -/
theorem weight_pos_le_two (n s j : ℕ) (hs : 0 < s) (hsn : s ≤ n) (hj : j < s) :
    0 < weight n s j ∧ weight n s j ≤ 2 := by
  have hn : 0 < n := hs.trans_le hsn
  have hsize := groupSize_pos n s j hs hsn hj
  have hsR : 0 < (s : ℝ) := by exact_mod_cast hs
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsizeR : 0 < (groupSize n s j : ℝ) := by exact_mod_cast hsize
  have hq : (1 : ℝ) ≤ (n / s : ℕ) := by exact_mod_cast Nat.div_pos hsn hs
  have hrem : (n % s : ℕ) < s := Nat.mod_lt n hs
  have hremR : (n % s : ℝ) < (s : ℝ) := by exact_mod_cast hrem
  have hdecomp : (n % s : ℝ) + (s : ℝ) * (n / s : ℕ) = (n : ℝ) := by
    exact_mod_cast Nat.mod_add_div n s
  have hqsize : ((n / s : ℕ) : ℝ) ≤ groupSize n s j := by
    exact_mod_cast (groupSize_bounds n s j hs hj).1
  have hsq : (s : ℝ) ≤ (s : ℝ) * (n / s : ℕ) :=
    le_mul_of_one_le_right hsR.le hq
  have hsqsize := mul_le_mul_of_nonneg_left hqsize hsR.le
  constructor
  · exact div_pos hnR (mul_pos hsR hsizeR)
  · unfold weight
    apply (div_le_iff₀ (mul_pos hsR hsizeR)).mpr
    nlinarith

theorem size_mul_weight (n s j : ℕ) (hs : 0 < s) (hsn : s ≤ n) (hj : j < s) :
    (groupSize n s j : ℝ) * weight n s j = (n : ℝ) / s := by
  have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  have hsizeR : (groupSize n s j : ℝ) ≠ 0 := by
    exact_mod_cast (groupSize_pos n s j hs hsn hj).ne'
  unfold weight
  field_simp

/-- Vector-valued finite averages are preserved exactly, not merely up to a
constant. The identity simultaneously applies to scalar values and gradients. -/
theorem finite_average_preserved {V : Type*} [AddCommGroup V] [Module ℝ V]
    (n s : ℕ) (hs : 0 < s) (hsn : s ≤ n) (g : ℕ → V) :
    (1 / (n : ℝ)) • (∑ i ∈ Finset.range n, weight n s (i % s) • g (i % s)) =
      (1 / (s : ℝ)) • (∑ j ∈ Finset.range s, g j) := by
  have hn : 0 < n := hs.trans_le hsn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hmap : ∀ i ∈ Finset.range n, i % s ∈ Finset.range s := by
    intro i _
    exact Finset.mem_range.mpr (Nat.mod_lt i hs)
  have hfib := Finset.sum_fiberwise_of_maps_to' hmap
    (fun j => weight n s j • g j)
  rw [← hfib]
  have hgroup : (∑ j ∈ Finset.range s,
      ∑ _i ∈ (Finset.range n).filter (fun i => i % s = j), weight n s j • g j) =
      ∑ j ∈ Finset.range s, ((n : ℝ) / s) • g j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.sum_const, ← group, ← groupSize]
    rw [← Nat.cast_smul_eq_nsmul ℝ, ← mul_smul,
      size_mul_weight n s j hs hsn (Finset.mem_range.mp hj)]
  rw [hgroup, ← Finset.smul_sum, smul_smul]
  congr 1
  field_simp

/-- Replicated scalar component functions. -/
noncomputable def component {Z : Type*} (n s i : ℕ) (g : ℕ → Z → ℝ) (z : Z) : ℝ :=
  weight n s (i % s) • g (i % s) z

/-- The actual Fréchet derivative scales by the same public weight. -/
theorem hasFDerivAt_component {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (n s i : ℕ) (g : ℕ → Z → ℝ) (z : Z) (D : Z →L[ℝ] ℝ)
    (hg : HasFDerivAt (g (i % s)) D z) :
    HasFDerivAt (component n s i g) (weight n s (i % s) • D) z := by
  exact hg.const_smul (weight n s (i % s))

/-- The factor of two bound gives the individual-smoothness transfer whenever
the source gradient has Lipschitz constant at most `L/2`. The statement applies
to the full joint gradient and arbitrary points in its prescribed domain. -/
theorem replicated_gradient_difference_bound {Z E : Type*}
    [SeminormedAddCommGroup Z] [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (n s : ℕ) (hs : 0 < s) (hsn : s ≤ n)
    (L : ℝ) (hL : 0 ≤ L) (G : ℕ → Z → E)
    (hG : ∀ j < s, ∀ z z', ‖G j z - G j z'‖ ≤ (L / 2) * ‖z - z'‖)
    (i : ℕ) (z z' : Z) :
    ‖weight n s (i % s) • G (i % s) z -
      weight n s (i % s) • G (i % s) z'‖ ≤ L * ‖z - z'‖ := by
  have hj := Nat.mod_lt i hs
  have hw := weight_pos_le_two n s (i % s) hs hsn hj
  have hfac : 0 ≤ (L / 2) * ‖z - z'‖ :=
    mul_nonneg (div_nonneg hL (by norm_num)) (norm_nonneg _)
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hw.1.le]
  calc
    weight n s (i % s) * ‖G (i % s) z - G (i % s) z'‖ ≤
        weight n s (i % s) * ((L / 2) * ‖z - z'‖) :=
      mul_le_mul_of_nonneg_left (hG (i % s) hj z z') hw.1.le
    _ ≤ 2 * ((L / 2) * ‖z - z'‖) := mul_le_mul_of_nonneg_right hw.2 hfac
    _ = L * ‖z - z'‖ := by ring

/-- In particular the actual scalar average objective is identical at every
point. Thus every property defined only by that average is preserved. -/
theorem component_average_preserved {Z : Type*}
    (n s : ℕ) (hs : 0 < s) (hsn : s ≤ n) (g : ℕ → Z → ℝ) (z : Z) :
    (1 / (n : ℝ)) * (∑ i ∈ Finset.range n, component n s i g z) =
      (1 / (s : ℝ)) * (∑ j ∈ Finset.range s, g j z) := by
  simpa only [component, smul_eq_mul] using
    finite_average_preserved n s hs hsn (fun j => g j z)

/-- An oracle query carries the component index and an arbitrary query point. -/
noncomputable def replicatedOracle {Z R : Type*} [SMul ℝ R]
    (n s : ℕ) (oracle : ℕ → Z → R) (q : ℕ × Z) : R :=
  weight n s (q.1 % s) • oracle (q.1 % s) q.2

/-- This simulator makes exactly one source oracle evaluation per target query.
`R` may be the tuple consisting of value and the full joint gradient. -/
noncomputable def oneQuerySimulator {Z R : Type*} [SMul ℝ R]
    (n s : ℕ) (oracle : ℕ → Z → R) (q : ℕ × Z) : R :=
  let sourceReply := oracle (q.1 % s) q.2
  weight n s (q.1 % s) • sourceReply

theorem exact_one_query_reply {Z R : Type*} [SMul ℝ R]
    (n s : ℕ) (oracle : ℕ → Z → R) (q : ℕ × Z) :
    oneQuerySimulator n s oracle q = replicatedOracle n s oracle q := rfl

/-- A finite adaptive interaction. The next query may depend on every earlier
query and reply. A private random seed can be held fixed in the policy. -/
def transcript {Q R : Type*} (oracle : Q → R)
    (policy : List (Q × R) → Q) : ℕ → List (Q × R)
  | 0 => []
  | k + 1 =>
    let hist := transcript oracle policy k
    let q := policy hist
    hist ++ [(q, oracle q)]

/-- Pointwise equality of replies gives equality of every adaptive transcript. -/
theorem transcript_eq_of_reply_eq {Q R : Type*} (left right : Q → R)
    (policy : List (Q × R) → Q) (hreply : ∀ q, left q = right q) :
    ∀ k, transcript left policy k = transcript right policy k := by
  have horacle : left = right := funext hreply
  subst right
  intro k
  rfl

/-- Exact chronological simulation for every budget and adaptive policy. -/
theorem exact_adaptive_transcript {Z R : Type*} [SMul ℝ R]
    (n s : ℕ) (oracle : ℕ → Z → R)
    (policy : List ((ℕ × Z) × R) → ℕ × Z) (k : ℕ) :
    transcript (oneQuerySimulator n s oracle) policy k =
      transcript (replicatedOracle n s oracle) policy k :=
  transcript_eq_of_reply_eq _ _ policy (exact_one_query_reply n s oracle) k

/-- An arbitrary final output, including one never queried, is preserved. -/
theorem exact_adaptive_output {Z R O : Type*} [SMul ℝ R]
    (n s : ℕ) (oracle : ℕ → Z → R)
    (policy : List ((ℕ × Z) × R) → ℕ × Z)
    (output : List ((ℕ × Z) × R) → O) (k : ℕ) :
    output (transcript (oneQuerySimulator n s oracle) policy k) =
      output (transcript (replicatedOracle n s oracle) policy k) := by
  rw [exact_adaptive_transcript]

/-- A budgeted policy can either terminate with an arbitrary output or request
a new query, based on the entire history. `none` means its public budget ran out
before termination. No queried-span restriction is imposed on outputs. -/
def adaptiveExecute {Q R O : Type*} (oracle : Q → R)
    (policy : List (Q × R) → O ⊕ Q) : ℕ → List (Q × R) → Option (O × List (Q × R))
  | 0, hist => match policy hist with
    | .inl output => some (output, hist)
    | .inr _ => none
  | k + 1, hist => match policy hist with
    | .inl output => some (output, hist)
    | .inr q => adaptiveExecute oracle policy k (hist ++ [(q, oracle q)])

/-- Exact reply simulation also preserves adaptive stopping, arbitrary final
outputs, and budget exhaustion. Quantification over the policy is pointwise in
any fixed private random seed. -/
theorem exact_adaptive_stopping {Z R O : Type*} [SMul ℝ R]
    (n s : ℕ) (oracle : ℕ → Z → R)
    (policy : List ((ℕ × Z) × R) → O ⊕ (ℕ × Z))
    (k : ℕ) (hist : List ((ℕ × Z) × R)) :
    adaptiveExecute (oneQuerySimulator n s oracle) policy k hist =
      adaptiveExecute (replicatedOracle n s oracle) policy k hist := rfl

end Replication
end NCConcave16991
