import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

namespace RandomizedFO2003

open Polynomial Set

theorem polynomial_root_between_opposite_signs (p : Polynomial ℝ) {a b : ℝ}
    (hab : a < b) (hsign : p.eval a * p.eval b < 0) :
    ∃ c ∈ Ioo a b, p.eval c = 0 := by
  rcases mul_neg_iff.mp hsign with h | h
  · exact intermediate_value_Ioo' hab.le p.continuousOn ⟨h.2, h.1⟩
  · exact intermediate_value_Ioo hab.le p.continuousOn ⟨h.1, h.2⟩

/-- Alternation at n+2 decreasing nodes forces n+1 distinct roots of a
polynomial. If its degree is at most n+1, its derivative cannot vanish to the
right of all those nodes. This is the root-counting core of the endpoint
Chebyshev derivative inequality. -/
theorem derivative_ne_zero_of_alternating_nodes
    (n : ℕ) (p : Polynomial ℝ) (x : Fin (n + 2) → ℝ) (b : ℝ)
    (hx : StrictAnti x) (hxb : ∀ i, x i ≤ b)
    (hdeg : p.natDegree ≤ n + 1)
    (hsign : ∀ i : Fin (n + 1), p.eval (x i.succ) * p.eval (x i.castSucc) < 0) :
    p.derivative.eval b ≠ 0 := by
  classical
  intro hdb
  have hroots : ∀ i : Fin (n + 1), ∃ r ∈ Ioo (x i.succ) (x i.castSucc), p.eval r = 0 := by
    intro i
    apply polynomial_root_between_opposite_signs p (hx (by simp)) (hsign i)
  choose r hr hpr using hroots
  have hranti : StrictAnti r := by
    intro i j hij
    have hnodes : x j.castSucc ≤ x i.succ := hx.antitone (by
      change i.val + 1 ≤ j.val
      exact hij)
    exact (hr j).2.trans_le (hnodes.trans (hr i).1.le)
  have hrb (i : Fin (n + 1)) : r i < b := (hr i).2.trans_le (hxb i.castSucc)
  have hcrit : ∀ i : Fin n, ∃ c ∈ Ioo (r i.succ) (r i.castSucc), p.derivative.eval c = 0 := by
    intro i
    obtain ⟨c, hc, hdc⟩ := exists_hasDerivAt_eq_zero
      (hranti (by simp)) p.continuousOn ((hpr i.succ).trans (hpr i.castSucc).symm)
      (fun y _ => p.hasDerivAt y)
    exact ⟨c, hc, hdc⟩
  choose c hc hpc using hcrit
  have hcanti : StrictAnti c := by
    intro i j hij
    have hnodes : r j.castSucc ≤ r i.succ := hranti.antitone (by
      change i.val + 1 ≤ j.val
      exact hij)
    exact (hc j).2.trans_le (hnodes.trans (hc i).1.le)
  have hcb (i : Fin n) : c i < b := (hc i).2.trans (hrb i.castSucc)
  let z : Fin (n + 1) → ℝ := Fin.snoc c b
  have hz : Function.Injective z := by
    intro i j hij
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => rfl
      | cast j =>
        have he : b = c j := by simpa [z] using hij
        exact False.elim ((hcb j).ne he.symm)
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        have he : c i = b := by simpa [z] using hij
        exact False.elim ((hcb i).ne he)
      | cast j =>
        have he : c i = c j := by simpa [z] using hij
        exact congrArg Fin.castSucc (hcanti.injective he)
  have hzroots : ∀ i, p.derivative.eval (z i) = 0 := by
    intro i
    induction i using Fin.lastCases with
    | last => simpa [z] using hdb
    | cast i => simpa [z] using hpc i
  have hzdeg : p.derivative.natDegree < Fintype.card (Fin (n + 1)) := by
    have h := p.natDegree_derivative_le
    simp only [Fintype.card_fin]
    omega
  have hzero := p.derivative.eq_zero_of_natDegree_lt_card_of_eval_eq_zero hz hzroots hzdeg
  have hpconst := Polynomial.eq_C_of_derivative_eq_zero hzero
  have hbad := hsign (0 : Fin (n + 1))
  rw [hpconst] at hbad
  simp only [eval_C] at hbad
  nlinarith [sq_nonneg (p.coeff 0)]

end RandomizedFO2003
