import RandomizedFO2003.ResidualWitness

namespace RandomizedFO2003

open Polynomial Set
open scoped BigOperators

/-- The finite design and fixed residual used before drawing any random rotation
or right-hand side. Every field is established by `exists_finite_spectral_design`
from the preceding uniform-approximation statement. -/
structure FiniteSpectralDesign (m : ℕ) (γ L e : ℝ) where
  size : ℕ
  size_le : size ≤ 2 * m + 2
  node : Fin size → ℝ
  weight : Fin size → ℝ
  distinct : Function.Injective node
  node_mem : ∀ j, node j ∈ Icc γ L
  weight_pos : ∀ j, 0 < weight j
  weight_sum : ∑ j, weight j = 1
  pstar : Polynomial ℝ
  degree_lt : pstar.natDegree < m
  orthogonal : ∀ q : Polynomial ℝ, q.natDegree < m →
    weightedPair weight (fun j => (node j)⁻¹ - pstar.eval (node j))
      (fun j => q.eval (node j)) = 0
  approximation_lower : ∀ q : Polynomial ℝ, q.natDegree < m →
    e ^ 2 ≤ weightedEnergy weight (fun j => (node j)⁻¹ - q.eval (node j))
  least_squares : ∀ q : Polynomial ℝ, q.natDegree < m →
    weightedEnergy weight (fun j => (node j)⁻¹ - pstar.eval (node j)) ≤
      weightedEnergy weight (fun j => (node j)⁻¹ - q.eval (node j))
  inverse_pairing : weightedPair weight (fun j => (node j)⁻¹ - pstar.eval (node j))
      (fun j => (node j)⁻¹) =
    weightedEnergy weight (fun j => (node j)⁻¹ - pstar.eval (node j))

/-- Lemma dual together with the fixed-residual construction, using a corrected
convex separation proof. The sole approximation input is Lemma markov's uniform
lower bound; there is no assumed measure, finite design or minimizer. -/
theorem exists_finite_spectral_design
    (m : ℕ) (hm : 1 ≤ m) (γ L e : ℝ) (hγ : 0 < γ) (he : 0 < e)
    (hgap : ∀ p : Polynomial ℝ, p.natDegree < m →
      ∃ x ∈ Icc γ L, e ≤ |x⁻¹ - p.eval x|) :
    Nonempty (FiniteSpectralDesign m γ L e) := by
  obtain ⟨J, hJ, node, weight, hinj, hnode, hw, hsum, hbound⟩ :=
    finite_inverse_spectral_design m hm γ L e hγ he hgap
  obtain ⟨pstar, hdeg, horth, hmin, hpair⟩ :=
    exists_least_squares_residual m hm node weight (fun j => (node j)⁻¹) (fun j => (hw j).le)
  exact ⟨{
    size := J
    size_le := hJ
    node := node
    weight := weight
    distinct := hinj
    node_mem := hnode
    weight_pos := hw
    weight_sum := hsum
    pstar := pstar
    degree_lt := hdeg
    orthogonal := horth
    approximation_lower := hbound
    least_squares := hmin
    inverse_pairing := hpair
  }⟩

namespace FiniteSpectralDesign

variable {m : ℕ} {γ L e : ℝ} (D : FiniteSpectralDesign m γ L e)

noncomputable def residual (j : Fin D.size) : ℝ := (D.node j)⁻¹ - D.pstar.eval (D.node j)

theorem residual_energy_lower : e ^ 2 ≤ weightedEnergy D.weight D.residual :=
  D.approximation_lower D.pstar D.degree_lt

theorem residual_energy_pos (he : 0 < e) : 0 < weightedEnergy D.weight D.residual :=
  (sq_pos_of_pos he).trans_le D.residual_energy_lower

theorem residual_nonzero (he : 0 < e) : D.residual ≠ 0 := by
  intro hzero
  have h := D.residual_energy_pos he
  simp [weightedEnergy, hzero] at h

/-- On any relative weight event of accuracy below 1, the normalization of the
residual is well-defined. This is a deterministic fact about the actual design. -/
theorem empirical_residual_energy_pos (he : 0 < e)
    (ω : Fin D.size → ℝ) (δ : ℝ) (hδ : δ < 1)
    (hweight : ∀ j, |ω j - D.weight j| ≤ δ * D.weight j) :
    0 < weightedEnergy ω D.residual := by
  have h := (weighted_energy_stability D.weight ω D.residual δ hweight).1
  have hp : 0 < (1 - δ) * weightedEnergy D.weight D.residual :=
    mul_pos (sub_pos.mpr hδ) (D.residual_energy_pos he)
  exact hp.trans_le h

end FiniteSpectralDesign
end RandomizedFO2003
