import RandomizedFO2003.FiniteDual
import RandomizedFO2003.MergeWeights
import Mathlib.Algebra.Polynomial.ofFn
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Topology.Algebra.Polynomial

namespace RandomizedFO2003

open Set Polynomial
open scoped BigOperators

def powerFeature (m : ℕ) (x : ℝ) : Fin m → ℝ := fun i => x ^ i.val

theorem continuous_powerFeature (m : ℕ) : Continuous (powerFeature m) := by
  apply continuous_pi
  intro i
  exact continuous_id.pow i.val

theorem ofFn_eval {m : ℕ} (c : Fin m → ℝ) (x : ℝ) :
    (Polynomial.ofFn m c).eval x = ∑ i, c i * x ^ i.val := by
  rw [Polynomial.ofFn_eq_sum_monomial, Polynomial.eval_finset_sum]
  simp [Polynomial.eval_monomial]

theorem linear_powerFeature_polynomial {m : ℕ} (hm : 1 ≤ m)
    (q : (Fin m → ℝ) →L[ℝ] ℝ) :
    ∃ p : Polynomial ℝ, p.natDegree < m ∧ ∀ x, p.eval x = q (powerFeature m x) := by
  classical
  let coeff : Fin m → ℝ := fun i => q (Pi.single i 1)
  refine ⟨Polynomial.ofFn m coeff, Polynomial.ofFn_natDegree_lt hm _, ?_⟩
  intro x
  have hdecomp : powerFeature m x =
      ∑ i : Fin m, (x ^ i.val) • (Pi.single i (1 : ℝ) : Fin m → ℝ) := by
    ext j
    simp [powerFeature, Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
  rw [Polynomial.ofFn_eq_sum_monomial, Polynomial.eval_finset_sum, hdecomp, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [coeff, Polynomial.eval_monomial, map_smul, mul_comm]

theorem polynomial_powerFeature_linear {m : ℕ} (p : Polynomial ℝ) (hp : p.natDegree < m) :
    ∃ q : (Fin m → ℝ) →L[ℝ] ℝ, ∀ x, q (powerFeature m x) = p.eval x := by
  refine ⟨∑ i : Fin m, p.coeff i.val • ContinuousLinearMap.proj i, ?_⟩
  intro x
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, powerFeature]
  rw [Polynomial.eval_eq_sum_range' hp]
  exact Fin.sum_univ_eq_sum_range (fun i => p.coeff i * x ^ i) m

/-- The finite spectral-design implication used in Lemma dual.
Only the uniform polynomial approximation lower bound is assumed. The positive
weights, distinct nodes and support bound are all constructed in this proof.
The sharper support bound m+2 implies the paper's 2*m+2 bound. -/
theorem finite_inverse_spectral_design
    (m : ℕ) (hm : 1 ≤ m) (γ L e : ℝ) (hγ : 0 < γ) (he : 0 < e)
    (hgap : ∀ p : Polynomial ℝ, p.natDegree < m →
      ∃ x ∈ Icc γ L, e ≤ |x⁻¹ - p.eval x|) :
    ∃ J : ℕ, J ≤ 2 * m + 2 ∧
      ∃ (lam ν : Fin J → ℝ), Function.Injective lam ∧
        (∀ j, lam j ∈ Icc γ L) ∧ (∀ j, 0 < ν j) ∧ (∑ j, ν j = 1) ∧
        ∀ p : Polynomial ℝ, p.natDegree < m →
          e ^ 2 ≤ ∑ j, ν j * ((lam j)⁻¹ - p.eval (lam j)) ^ 2 := by
  have hinv : ContinuousOn (fun x : ℝ => x⁻¹) (Icc γ L) := by
    apply continuousOn_id.inv₀
    intro x hx
    exact ne_of_gt (hγ.trans_le hx.1)
  have hgap' : ∀ q : (Fin m → ℝ) →L[ℝ] ℝ,
      ∃ x ∈ Icc γ L, e ≤ |x⁻¹ - q (powerFeature m x)| := by
    intro q
    obtain ⟨p, hp, heval⟩ := linear_powerFeature_polynomial hm q
    obtain ⟨x, hx, hg⟩ := hgap p hp
    exact ⟨x, hx, by simpa only [heval] using hg⟩
  obtain ⟨n, hn, node, w, hnode, hw, hsum, hbound⟩ :=
    exists_finite_dual_design isCompact_Icc hinv (continuous_powerFeature m).continuousOn he hgap'
  obtain ⟨J, hJn, lam, ν, hinj, hrange, hν, hmerge⟩ := merge_positive_weights node w hw
  refine ⟨J, ?_, lam, ν, hinj, ?_, hν, ?_, ?_⟩
  · simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hn
    omega
  · intro j
    obtain ⟨i, hi⟩ := hrange j
    rw [← hi]
    exact hnode i
  · simpa using (hmerge (fun _ => 1)).trans (by simpa using hsum)
  · intro p hp
    obtain ⟨q, hq⟩ := polynomial_powerFeature_linear p hp
    have hb := hbound q
    simp_rw [hq] at hb
    rw [hmerge (fun x => (x⁻¹ - p.eval x) ^ 2)]
    exact hb

end RandomizedFO2003
