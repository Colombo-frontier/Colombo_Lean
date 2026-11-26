import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic

open scoped BigOperators ContDiff

namespace FullJet

noncomputable def quadratic (μ c x : ℝ) : ℝ := μ / 2 * x ^ 2 - c * x

theorem quadratic_hasDerivAt (μ c x : ℝ) :
    HasDerivAt (quadratic μ c) (μ * x - c) x := by
  convert (((hasDerivAt_id x).pow 2).const_mul (μ / 2)).sub
    ((hasDerivAt_id x).const_mul c) using 1 <;> simp [quadratic] <;> ring

theorem quadratic_deriv (μ c : ℝ) : deriv (quadratic μ c) = fun x => μ * x - c := by
  funext x
  exact (quadratic_hasDerivAt μ c x).deriv

theorem quadratic_second_deriv (μ c : ℝ) : iteratedDeriv 2 (quadratic μ c) = fun _ => μ := by
  rw [iteratedDeriv_succ', quadratic_deriv]
  funext x
  simpa using (((hasDerivAt_id x).const_mul μ).sub_const c).deriv

theorem quadratic_higher_deriv (μ c : ℝ) (k : ℕ) :
    iteratedDeriv (k + 3) (quadratic μ c) = 0 := by
  induction k with
  | zero =>
    rw [show 0 + 3 = 2 + 1 from rfl, iteratedDeriv_succ, quadratic_second_deriv]
    ext x
    simp
  | succ k ih =>
    rw [show k + 1 + 3 = (k + 3) + 1 by omega, iteratedDeriv_succ, ih]
    ext x
    simp

theorem quadratic_complete_square (μ c x : ℝ) (hμ : μ ≠ 0) :
    quadratic μ c x = μ / 2 * (x - c / μ) ^ 2 - c ^ 2 / (2 * μ) := by
  unfold quadratic
  field_simp
  <;> ring

theorem quadratic_global_minimum (μ c : ℝ) (hμ : 0 < μ) :
    (∀ x, quadratic μ c (c / μ) ≤ quadratic μ c x) ∧
    quadratic μ c 0 - quadratic μ c (c / μ) = c ^ 2 / (2 * μ) := by
  constructor
  · intro x
    rw [quadratic_complete_square μ c _ hμ.ne', quadratic_complete_square μ c _ hμ.ne']
    nlinarith [sq_nonneg (x - c / μ)]
  · rw [quadratic_complete_square μ c (c / μ) hμ.ne']
    simp [quadratic]

/-- The two possible gradients cannot both be small at the same output. -/
theorem two_sign_gradient_barrier (z g : ℝ) : g ≤ |z - g| ∨ g ≤ |z + g| := by
  by_contra h
  push_neg at h
  have h₁ := (abs_lt.mp h.1).1
  have h₂ := (abs_lt.mp h.2).2
  linarith

theorem two_sign_expected_barrier (z g : ℝ) : g ≤ (|z - g| + |z + g|) / 2 := by
  have h₁ := le_abs_self (z + g)
  have h₂ := neg_le_abs (z - g)
  linarith

/-- The rare-component quadratic has exactly the prescribed positive gap. -/
theorem rare_gap_parameters (Δ ε : ℝ) (hΔ : 0 < Δ) (hε : 0 < ε) :
    let g := 4 * ε
    let μ := g ^ 2 / (2 * Δ)
    0 < μ ∧ g ^ 2 / (2 * μ) = Δ := by
  dsimp
  constructor
  · positivity
  · field_simp
    <;> ring

/-- A state includes the full prior transcript and a fixed private random seed.
No restriction is imposed on adaptive queries or internal state transitions. -/
def oracleRun {State Query Reply : Type*}
    (query : State → Query) (update : State → Reply → State)
    (oracle : Query → Reply) (initial : State) : ℕ → State
  | 0 => initial
  | k + 1 => let s := oracleRun query update oracle initial k
             update s (oracle (query s))

/-- Exact coupling of adaptive transcripts along the reference oracle path. -/
theorem oracleRun_eq_of_agree {State Query Reply : Type*}
    (query : State → Query) (update : State → Reply → State)
    (oracle reference : Query → Reply) (initial : State) (q : ℕ)
    (h : ∀ t < q, oracle (query (oracleRun query update reference initial t)) =
      reference (query (oracleRun query update reference initial t))) :
    oracleRun query update oracle initial q = oracleRun query update reference initial q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    have heq := ih (fun t ht => h t (by omega))
    simp only [oracleRun, heq, h q (Nat.lt_succ_self q)]

/-- A reference transcript queries at most `q` distinct component indices. -/
theorem queried_indices_card_le {Index : Type*} [DecidableEq Index]
    (indices : ℕ → Index) (q : ℕ) :
    ((Finset.range q).image indices).card ≤ q :=
  (Finset.card_image_le).trans_eq (Finset.card_range q)

/-- Every unqueried rare index gives identical full adaptive runs for both signs. -/
theorem rare_index_coupling {State Index Point Reply : Type*} [DecidableEq Index]
    (query : State → Index × Point) (update : State → Reply → State)
    (oracle reference : Index × Point → Reply) (initial : State) (q : ℕ) (J : Index)
    (hrare : ∀ z, z.1 ≠ J → oracle z = reference z)
    (hmiss : J ∉ (Finset.range q).image
      (fun t => (query (oracleRun query update reference initial t)).1)) :
    oracleRun query update oracle initial q = oracleRun query update reference initial q := by
  apply oracleRun_eq_of_agree
  intro t ht
  apply hrare
  intro heq
  apply hmiss
  exact Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr ht, heq⟩

end FullJet
