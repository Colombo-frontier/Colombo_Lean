import FullJet.FixedTables
import FullJet.AdaptiveRows

namespace FullJet

noncomputable def fixedColumnLaw (n k : ℕ) (hk : k ≤ n) : PMF (FixedColumn n k) := by
  letI := fixedColumn_nonempty hk
  exact PMF.uniformOfFintype _

/-- Forgetting the fixed-cardinality proof yields the concrete subset law used
in the adaptive sampling theorems. -/
theorem fixedColumnLaw_forget (n k : ℕ) (hk : k ≤ n) :
    (fixedColumnLaw n k hk).map Subtype.val =
      fixedSizeLaw (Finset.univ : Finset (Fin n)) k (by simpa using hk) := by
  classical
  letI := fixedColumn_nonempty hk
  unfold fixedColumnLaw PMF.uniformOfFintype fixedSizeLaw
  rw [uniformOfFinset_map_injOn _ _ Subtype.val (Subtype.val_injective.injOn)]
  congr 1
  ext S
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_powersetCard,
    Finset.subset_univ]
  constructor
  · rintro ⟨T, rfl⟩
    exact T.property
  · intro hcard
    exact ⟨⟨S, hcard⟩, rfl⟩

theorem powersetCard_image_compl (n k : ℕ) (hk : k ≤ n) :
    (((Finset.univ : Finset (Fin n)).powersetCard k).image fun S => Sᶜ) =
      Finset.univ.powersetCard (n - k) := by
  ext S
  simp only [Finset.mem_image, Finset.mem_powersetCard, Finset.subset_univ, true_and]
  have hcard (R : Finset (Fin n)) : Rᶜ.card = n - R.card := by
    rw [Finset.compl_eq_univ_sdiff, Finset.card_sdiff (Finset.subset_univ _)]
    simp
  constructor
  · rintro ⟨R, hR, rfl⟩
    rw [hcard, hR]
  · intro hS
    refine ⟨Sᶜ, ?_, compl_compl S⟩
    rw [hcard, hS]
    omega

/-- Negating an entire fixed column changes its positive count from `k` to
`n-k` and leaves its distribution uniform. -/
theorem fixedSizeLaw_compl (n k : ℕ) (hk : k ≤ n) :
    (fixedSizeLaw (Finset.univ : Finset (Fin n)) k (by simpa using hk)).map (fun S => Sᶜ) =
      fixedSizeLaw Finset.univ (n - k) (by simp) := by
  classical
  unfold fixedSizeLaw
  rw [uniformOfFinset_map_injOn _ _ (fun S => Sᶜ) (compl_injective.injOn)]
  congr 1
  exact powersetCard_image_compl n k hk

theorem columnSign_compl {n : ℕ} (S : Finset (Fin n)) (i : Fin n) :
    columnSign Sᶜ i = -columnSign S i := by
  simp only [columnSign, Finset.mem_compl]
  by_cases hi : i ∈ S <;> simp [hi]

/-- The observed positive-position law in the negative-hidden-sign case. -/
theorem fixedColumnLaw_negated (n k : ℕ) (hk : k ≤ n) :
    (fixedColumnLaw n k hk).map (fun S => S.valᶜ) =
      fixedSizeLaw (Finset.univ : Finset (Fin n)) (n - k) (by simp) := by
  calc
    _ = ((fixedColumnLaw n k hk).map Subtype.val).map (fun S : Finset (Fin n) => Sᶜ) :=
      (PMF.map_comp Subtype.val (fixedColumnLaw n k hk) (fun S : Finset (Fin n) => Sᶜ)).symm
    _ = _ := by rw [fixedColumnLaw_forget, fixedSizeLaw_compl n k hk]

end FullJet
