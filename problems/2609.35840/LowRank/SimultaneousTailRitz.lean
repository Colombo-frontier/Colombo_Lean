import LowRank.TailRitzConfidence
import LowRank.SimultaneousKrylovRitz

/-! All head Ritz errors share a fixed tail scale and one Krylov run.
The positive-head and positive-cutoff hypotheses are explicit. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix BigOperators ENNReal
noncomputable section

def krylovTailRitzEvent {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℝ)
    (sp : OrderedMatrixSpectrum (Aᵀ * A)) (k s n : ℕ) (hk : k ≤ b) (γ L : ℝ) :
    Set (Matrix (Fin a) (Fin s) ℝ) :=
  {U | ∀ j : Fin k, sp.value (lastColumnIndex b k hk j) - (γ / 2) * L ≤
    (canonicalOrderedSpectrum b (symmetricRightGram (A *
      columnRangeProjector (krylovRightBlocks (krylovBlockData A n U))))).value
        (lastColumnIndex b k hk j)}

theorem measurableSet_krylovTailRitzEvent {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℝ)
    (sp : OrderedMatrixSpectrum (Aᵀ * A)) (k s n : ℕ) (hk : k ≤ b) (γ L : ℝ) :
    MeasurableSet (krylovTailRitzEvent A sp k s n hk γ L) := by
  have he : krylovTailRitzEvent A sp k s n hk γ L =
      ⋂ j : Fin k, {U | sp.value (lastColumnIndex b k hk j) - (γ / 2) * L ≤
        (canonicalOrderedSpectrum b (symmetricRightGram (A *
          columnRangeProjector (krylovRightBlocks (krylovBlockData A n U))))).value
            (lastColumnIndex b k hk j)} := by
    ext U
    simp only [krylovTailRitzEvent, Set.mem_setOf_eq, Set.mem_iInter]
  rw [he]
  exact MeasurableSet.iInter (fun j => measurableSet_le measurable_const (measurable_krylovRitzValue A _))

theorem krylov_simultaneous_tail_ritz_confidence_le {a m k s n : ℕ}
    (A : Matrix (Fin a) (Fin (m + k)) ℝ) (sp : OrderedMatrixSpectrum (Aᵀ * A))
    (hp : ∀ j : Fin k, 0 < sp.value (j.natAdd m)) (hs : 2 * k + 2 ≤ s)
    {L γ q : ℝ} (hL : 0 < L) (hl : ∀ i : Fin m, sp.value (i.castAdd k) ≤ L)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hq : 0 < q)
    (hn : chebyshevFilterDegree γ (confidentRitzTolerance γ q s (m + k)) < n) :
    (iidMatrixLaw a s 1) (krylovTailRitzEvent A sp k s n (by omega) γ L)ᶜ ≤
      ENNReal.ofReal ((k : ℝ) * (2 / q)) := by
  let E : Fin k → Set (Matrix (Fin a) (Fin s) ℝ) := fun j => {U |
    (canonicalOrderedSpectrum (m + k) (symmetricRightGram (A *
      columnRangeProjector (krylovRightBlocks (krylovBlockData A n U))))).value (j.natAdd m) <
        sp.value (j.natAdd m) - (γ / 2) * L}
  have he : (krylovTailRitzEvent A sp k s n (by omega) γ L)ᶜ = ⋃ j : Fin k, E j := by
    ext U
    simp only [krylovTailRitzEvent, E, lastColumnIndex_add, Set.mem_compl_iff, Set.mem_setOf_eq,
      Set.mem_iUnion, not_forall, not_le]
  have hE (j : Fin k) : (iidMatrixLaw a s 1) (E j) ≤ ENNReal.ofReal (2 / q) :=
    krylov_gaussian_tail_ritz_index_confidence_le A sp hp hs j hL hl hγ hγ1 hq hn
  rw [he]
  calc
    _ ≤ ∑ j : Fin k, (iidMatrixLaw a s 1) (E j) := by
      simpa only [tsum_fintype] using measure_iUnion_le E
    _ ≤ ∑ _ : Fin k, ENNReal.ofReal (2 / q) := Finset.sum_le_sum (fun j _ => hE j)
    _ = _ := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun (_ : Fin k) _ => by positivity :
        ∀ j ∈ (Finset.univ : Finset (Fin k)), 0 ≤ (2 : ℝ) / q)]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem krylov_simultaneous_tail_ritz_bad_le {a m k s n : ℕ} (hk0 : 0 < k)
    (A : Matrix (Fin a) (Fin (m + k)) ℝ) (sp : OrderedMatrixSpectrum (Aᵀ * A))
    (hp : ∀ j : Fin k, 0 < sp.value (j.natAdd m)) (hs : 2 * k + 2 ≤ s)
    {L γ : ℝ} (hL : 0 < L) (hl : ∀ i : Fin m, sp.value (i.castAdd k) ≤ L)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hn : chebyshevFilterDegree γ (confidentRitzTolerance γ (40 * (k : ℝ)) s (m + k)) < n) :
    (iidMatrixLaw a s 1) (krylovTailRitzEvent A sp k s n (by omega) γ L)ᶜ ≤ 1 / 20 := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk0
  have h := krylov_simultaneous_tail_ritz_confidence_le A sp hp hs hL hl hγ hγ1
    (by positivity : 0 < 40 * (k : ℝ)) hn
  have he : (k : ℝ) * (2 / (40 * (k : ℝ))) = 1 / 20 := by field_simp; ring
  rw [he, ENNReal.ofReal_div_of_pos (by norm_num)] at h
  norm_num only [ENNReal.ofReal_one, ENNReal.ofReal_ofNat] at h
  exact h

theorem krylov_simultaneous_tail_ritz_success {a m k s n : ℕ} (hk0 : 0 < k)
    (A : Matrix (Fin a) (Fin (m + k)) ℝ) (sp : OrderedMatrixSpectrum (Aᵀ * A))
    (hp : ∀ j : Fin k, 0 < sp.value (j.natAdd m)) (hs : 2 * k + 2 ≤ s)
    {L γ : ℝ} (hL : 0 < L) (hl : ∀ i : Fin m, sp.value (i.castAdd k) ≤ L)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hn : chebyshevFilterDegree γ (confidentRitzTolerance γ (40 * (k : ℝ)) s (m + k)) < n) :
    19 / 20 ≤ (iidMatrixLaw a s 1).real (krylovTailRitzEvent A sp k s n (by omega) γ L) := by
  have hbad := krylov_simultaneous_tail_ritz_bad_le hk0 A sp hp hs hL hl hγ hγ1 hn
  have hr := ENNReal.toReal_mono (by norm_num : (1 / 20 : ℝ≥0∞) ≠ ∞) hbad
  change (iidMatrixLaw a s 1).real _ ≤ _ at hr
  rw [measureReal_compl (measurableSet_krylovTailRitzEvent A sp k s n (by omega) γ L),
    measureReal_univ_eq_one] at hr
  norm_num only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat] at hr
  linarith

theorem krylov_simultaneous_positive_tail_success {a m k s n : ℕ} (hm : 0 < m) (hk0 : 0 < k)
    (A : Matrix (Fin a) (Fin (m + k)) ℝ) (sp : OrderedMatrixSpectrum (Aᵀ * A))
    (hL : 0 < sp.value (⟨m - 1, by omega⟩ : Fin (m + k))) (hs : 2 * k + 2 ≤ s)
    {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hn : chebyshevFilterDegree γ (confidentRitzTolerance γ (40 * (k : ℝ)) s (m + k)) < n) :
    19 / 20 ≤ (iidMatrixLaw a s 1).real (krylovTailRitzEvent A sp k s n (by omega) γ
      (sp.value (⟨m - 1, by omega⟩ : Fin (m + k)))) := by
  apply krylov_simultaneous_tail_ritz_success hk0 A sp _ hs hL _ hγ hγ1 hn
  · intro j
    apply hL.trans_le (sp.increasing _)
    change m - 1 ≤ m + j.val
    omega
  · intro i
    apply sp.increasing
    change i.val ≤ m - 1
    omega

end
end LowRank
