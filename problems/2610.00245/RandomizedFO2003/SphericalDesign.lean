import RandomizedFO2003.SphereWeights

namespace RandomizedFO2003.Spherical

open MeasureTheory SpectralCoordinates
open scoped BigOperators ENNReal

/-- The complete spectral-weight concentration statement for a genuine sphere
law. Arbitrarily large multiplicities achieve any prescribed failure bound. -/
theorem exists_good_spherical_weights {J : ℕ} (ν : Fin J → ℝ)
    (hν : ∀ j, 0 < ν j) (hsum : ∑ j, ν j = 1)
    (δ ζ : ℝ) (hδ : 0 < δ) (hδone : δ ≤ 1) (hζ : 0 < ζ) (Rmin Nmin : ℕ) :
    ∃ K : Fin J → ℕ,
      (∀ j, 0 < K j ∧ Rmin ≤ K j) ∧ Nmin ≤ ∑ j, K j ∧ 0 < ∑ j, K j ∧
      (∀ᵐ u ∂sphereLaw (BlockSpace K), ‖u‖ = 1) ∧
      sphereLaw (BlockSpace K) {u | ∃ j, δ * ν j < |weight K u j - ν j|} ≤ ENNReal.ofReal ζ ∧
      1 - ENNReal.ofReal ζ ≤
        sphereLaw (BlockSpace K) {u | ∀ j, |weight K u j - ν j| ≤ δ * ν j} := by
  let η := δ / 4
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨R, hR⟩ := exists_nat_gt (max 1 (2 * (J : ℝ) / (η ^ 2 * ζ)))
  have hRpos : (0 : ℝ) < R := by
    have ht := (le_max_left (1 : ℝ) (2 * (J : ℝ) / (η ^ 2 * ζ))).trans_lt hR
    linarith
  have hlarge : 2 * (J : ℝ) ≤ (R : ℝ) * (η ^ 2 * ζ) := by
    apply (div_le_iff₀ (mul_pos (sq_pos_of_pos hη) hζ)).mp
    exact ((le_max_right _ _).trans_lt hR).le
  obtain ⟨K, hK, hN, htotal, happ⟩ := exists_relative_multiplicities ν hν hsum
    η hη (max R Rmin) Nmin
  haveI : Nonempty (Σ j, Fin (K j)) := Fintype.card_pos_iff.mp (by
    simpa only [Fintype.card_sigma, Fintype.card_fin] using htotal)
  have hRK (j : Fin J) : (R : ℝ) ≤ K j := by
    exact_mod_cast (Nat.le_max_left R Rmin).trans (hK j).2
  have hbound : (J : ℝ) * (2 / (η ^ 2 * (R : ℝ))) ≤ ζ := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (mul_pos (sq_pos_of_pos hη) hRpos)).mpr
    nlinarith [hlarge]
  have hbad : sphereLaw (BlockSpace K) {u | ∃ j, δ * ν j < |weight K u j - ν j|} ≤
      ENNReal.ofReal ζ := by
    calc
      _ ≤ ∑ j, ENNReal.ofReal (2 / (η ^ 2 * (K j : ℝ))) :=
        design_weights_bad_le K (fun j => (hK j).1) ν (fun j => (hν j).le)
          δ hδ hδone happ
      _ ≤ ∑ _j : Fin J, ENNReal.ofReal (2 / (η ^ 2 * (R : ℝ))) := by
        apply Finset.sum_le_sum
        intro j _
        apply ENNReal.ofReal_le_ofReal
        exact div_le_div_of_nonneg_left (by norm_num) (mul_pos (sq_pos_of_pos hη) hRpos)
          (mul_le_mul_of_nonneg_left (hRK j) (sq_nonneg η))
      _ = ENNReal.ofReal ((J : ℝ) * (2 / (η ^ 2 * (R : ℝ)))) := by
        simp [ENNReal.ofReal_mul, nsmul_eq_mul]
      _ ≤ _ := ENNReal.ofReal_le_ofReal hbound
  refine ⟨K, (fun j => ⟨(hK j).1, (Nat.le_max_right R Rmin).trans (hK j).2⟩),
    hN, htotal, ae_norm_one (BlockSpace K), hbad, ?_⟩
  have hcompl : {u : BlockSpace K | ∀ j, |weight K u j - ν j| ≤ δ * ν j} =
      {u : BlockSpace K | ∃ j, δ * ν j < |weight K u j - ν j|}ᶜ := by
    ext u
    simp
  rw [hcompl, prob_compl_eq_one_sub (measurable_bad_weights K ν δ)]
  exact tsub_le_tsub_left hbad 1

end RandomizedFO2003.Spherical

namespace RandomizedFO2003.FiniteSpectralDesign

open MeasureTheory SpectralCoordinates Spherical
open scoped BigOperators ENNReal

variable {m : ℕ} {γ L e : ℝ} (D : FiniteSpectralDesign m γ L e)

theorem choose_concentrated_multiplicities (δ ζ : ℝ)
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hζ : 0 < ζ) (R N : ℕ) :
    ∃ K : Fin D.size → ℕ,
      (∀ j, 0 < K j ∧ R ≤ K j) ∧ N ≤ ∑ j, K j ∧ 0 < ∑ j, K j ∧
      (∀ᵐ u ∂sphereLaw (BlockSpace K), ‖u‖ = 1) ∧
      sphereLaw (BlockSpace K) {u | ∃ j, δ * D.weight j <
        |SpectralCoordinates.weight K u j - D.weight j|} ≤ ENNReal.ofReal ζ ∧
      1 - ENNReal.ofReal ζ ≤ sphereLaw (BlockSpace K) {u | ∀ j,
        |SpectralCoordinates.weight K u j - D.weight j| ≤ δ * D.weight j} :=
  exists_good_spherical_weights D.weight D.weight_pos D.weight_sum δ ζ hδ hδone hζ R N

end RandomizedFO2003.FiniteSpectralDesign
