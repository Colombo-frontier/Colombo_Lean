import RandomizedFO2003.PolynomialDual
import RandomizedFO2003.Spectral
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace RandomizedFO2003

open Polynomial
open scoped BigOperators

noncomputable def weightedEmbed {J : ℕ} (ν : Fin J → ℝ) :
    (Fin J → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin J) where
  toFun f := (WithLp.equiv 2 (Fin J → ℝ)).symm (fun j => Real.sqrt (ν j) * f j)
  map_add' f g := by
    ext j
    simp [mul_add]
  map_smul' c f := by
    ext j
    simp [mul_comm, mul_left_comm, mul_assoc]

theorem inner_weightedEmbed {J : ℕ} (ν f g : Fin J → ℝ) (hν : ∀ j, 0 ≤ ν j) :
    inner (𝕜 := ℝ) (weightedEmbed ν f) (weightedEmbed ν g) = weightedPair ν f g := by
  simp only [PiLp.inner_apply, weightedPair]
  apply Finset.sum_congr rfl
  intro j _
  change (Real.sqrt (ν j) * g j) * (Real.sqrt (ν j) * f j) = ν j * f j * g j
  calc
    _ = (Real.sqrt (ν j)) ^ 2 * (f j * g j) := by ring
    _ = _ := by rw [Real.sq_sqrt (hν j)]; ring

noncomputable def polynomialEvalMap {J : ℕ} (lam : Fin J → ℝ) (m : ℕ) :
    (Fin m → ℝ) →ₗ[ℝ] (Fin J → ℝ) where
  toFun c j := ∑ i, c i * (lam j) ^ i.val
  map_add' c d := by
    ext j
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' a c := by
    ext j
    simp [Finset.mul_sum, mul_assoc]

theorem polynomialEvalMap_apply {J m : ℕ} (lam : Fin J → ℝ) (c : Fin m → ℝ) (j : Fin J) :
    polynomialEvalMap lam m c j = (Polynomial.ofFn m c).eval (lam j) :=
  (ofFn_eval c (lam j)).symm

/-- The residual polynomial is obtained by a genuine finite-dimensional
orthogonal projection. Existence and all short-polynomial orthogonality
conditions are proved, including for singular designs and zero weights. -/
theorem exists_orthogonal_residual {J : ℕ} (m : ℕ) (hm : 1 ≤ m)
    (lam ν f : Fin J → ℝ) (hν : ∀ j, 0 ≤ ν j) :
    ∃ pstar : Polynomial ℝ, pstar.natDegree < m ∧
      ∀ q : Polynomial ℝ, q.natDegree < m →
        weightedPair ν (fun j => f j - pstar.eval (lam j)) (fun j => q.eval (lam j)) = 0 := by
  let T := (weightedEmbed ν).comp (polynomialEvalMap lam m)
  let K := LinearMap.range T
  obtain ⟨z, hz, horth⟩ := Submodule.HasOrthogonalProjection.exists_orthogonal
    (K := K) (weightedEmbed ν f)
  obtain ⟨c, hc⟩ := hz
  refine ⟨Polynomial.ofFn m c, Polynomial.ofFn_natDegree_lt hm _, ?_⟩
  intro q hq
  let d := Polynomial.toFn m q
  have hqeq : Polynomial.ofFn m d = q := Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt hq
  have hevalc : polynomialEvalMap lam m c = fun j => (Polynomial.ofFn m c).eval (lam j) := by
    ext j
    exact polynomialEvalMap_apply lam c j
  have hevald : polynomialEvalMap lam m d = fun j => q.eval (lam j) := by
    ext j
    rw [polynomialEvalMap_apply, hqeq]
  have h := (K.mem_orthogonal' _).mp horth (T d) ⟨d, rfl⟩
  rw [← hc] at h
  change inner (𝕜 := ℝ) (weightedEmbed ν f - weightedEmbed ν (polynomialEvalMap lam m c))
    (weightedEmbed ν (polynomialEvalMap lam m d)) = 0 at h
  rw [← map_sub, inner_weightedEmbed ν _ _ hν, hevalc, hevald] at h
  exact h

theorem weighted_energy_sub_expansion {J : ℕ} (ν f p q : Fin J → ℝ) :
    weightedEnergy ν (f - q) = weightedEnergy ν (f - p) + weightedEnergy ν (p - q) +
      2 * (weightedPair ν (f - p) p - weightedPair ν (f - p) q) := by
  simp only [weightedEnergy, weightedPair, Pi.sub_apply]
  rw [← Finset.sum_sub_distrib, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem weighted_residual_pairing {J : ℕ} (ν f p : Fin J → ℝ)
    (horth : weightedPair ν (f - p) p = 0) :
    weightedPair ν (f - p) f = weightedEnergy ν (f - p) := by
  have heq : weightedPair ν (f - p) f =
      weightedEnergy ν (f - p) + weightedPair ν (f - p) p := by
    simp only [weightedPair, weightedEnergy, Pi.sub_apply, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simpa [horth] using heq

/-- Existence of the least-squares polynomial, its normal equations, and the
identity pairing the residual against the target. No minimizer is postulated. -/
theorem exists_least_squares_residual {J : ℕ} (m : ℕ) (hm : 1 ≤ m)
    (lam ν f : Fin J → ℝ) (hν : ∀ j, 0 ≤ ν j) :
    ∃ pstar : Polynomial ℝ, pstar.natDegree < m ∧
      (∀ q : Polynomial ℝ, q.natDegree < m →
        weightedPair ν (fun j => f j - pstar.eval (lam j)) (fun j => q.eval (lam j)) = 0) ∧
      (∀ q : Polynomial ℝ, q.natDegree < m →
        weightedEnergy ν (fun j => f j - pstar.eval (lam j)) ≤
          weightedEnergy ν (fun j => f j - q.eval (lam j))) ∧
      weightedPair ν (fun j => f j - pstar.eval (lam j)) f =
        weightedEnergy ν (fun j => f j - pstar.eval (lam j)) := by
  obtain ⟨p, hp, horth⟩ := exists_orthogonal_residual m hm lam ν f hν
  refine ⟨p, hp, horth, ?_, ?_⟩
  · intro q hq
    have hexp := weighted_energy_sub_expansion ν f (fun j => p.eval (lam j))
      (fun j => q.eval (lam j))
    have hp0 : weightedPair ν (f - fun j => p.eval (lam j)) (fun j => p.eval (lam j)) = 0 :=
      horth p hp
    have hq0 : weightedPair ν (f - fun j => p.eval (lam j)) (fun j => q.eval (lam j)) = 0 :=
      horth q hq
    rw [hp0, hq0, sub_self, mul_zero, add_zero] at hexp
    have hnonneg : 0 ≤ weightedEnergy ν (fun j => p.eval (lam j) - q.eval (lam j)) :=
      Finset.sum_nonneg (fun j _ => mul_nonneg (hν j) (sq_nonneg _))
    change weightedEnergy ν (f - fun j => p.eval (lam j)) ≤
      weightedEnergy ν (f - fun j => q.eval (lam j))
    rw [hexp]
    exact le_add_of_nonneg_right hnonneg
  · exact weighted_residual_pairing ν f (fun j => p.eval (lam j)) (horth p hp)

end RandomizedFO2003
