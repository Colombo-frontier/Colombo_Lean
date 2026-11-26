import FullJet.FixedColumnLaw
import FullJet.VectorRows

open scoped BigOperators ENNReal

namespace FullJet

abbrev HiddenColumnSample (n k : ℕ) := Bool × FixedColumn n k

/-- Reorganize the original table sample into its independent column samples. -/
def tableColumnEquiv (n D k : ℕ) : FixedTableSample n D k ≃ (Fin D → HiddenColumnSample n k) where
  toFun ω j := (ω.1 j, ω.2 j)
  invFun z := (fun j => (z j).1, fun j => (z j).2)
  left_inv ω := rfl
  right_inv z := by funext j; exact Prod.eta (z j)

noncomputable def hiddenColumnTableLaw (n D k : ℕ) (hk : k ≤ n) :
    PMF (Fin D → HiddenColumnSample n k) := by
  letI := fixedColumn_nonempty hk
  exact uniformPi (fun _ => Finset.univ) (fun _ => Finset.univ_nonempty)

/-- The Cartesian column law is exactly the pushforward of the hard table
distribution already used in the objective-function construction. -/
theorem fixedTableLaw_columns (n D k : ℕ) (hk : k ≤ n) :
    (fixedTableLaw n D k hk).map (tableColumnEquiv n D k) = hiddenColumnTableLaw n D k hk := by
  classical
  letI := fixedColumn_nonempty hk
  unfold fixedTableLaw hiddenColumnTableLaw uniformPi PMF.uniformOfFintype
  rw [uniformOfFinset_map_injOn _ _ _ (tableColumnEquiv n D k).injective.injOn]
  congr 1
  rw [Finset.image_univ_of_surjective (tableColumnEquiv n D k).surjective, Fintype.piFinset_univ]

def observedPositiveColumn {n k : ℕ} (z : HiddenColumnSample n k) : Finset (Fin n) :=
  if z.1 then z.2.val else z.2.valᶜ

theorem observedPositiveColumn_sign {n D k : ℕ} (ω : FixedTableSample n D k)
    (j : Fin D) (i : Fin n) :
    columnSign (observedPositiveColumn (tableColumnEquiv n D k ω j)) i =
      rareSign (ω.1 j) * columnSign (ω.2 j).val i := by
  cases h : ω.1 j <;> simp [observedPositiveColumn, tableColumnEquiv, h, rareSign, columnSign_compl]

def hiddenCompatibleSamples {n D k : ℕ} (ask : List (Fin D → Bool) → Fin n)
    (past rows : List (Fin D → Bool)) (j : Fin D) : Finset (HiddenColumnSample n k) :=
  Finset.univ.filter (fun z => compatibleColumn (vectorPositiveLabels ask past rows j)
    (vectorNegativeLabels ask past rows j) (observedPositiveColumn z))

theorem hiddenColumnTableLaw_history_feasible {n D k : ℕ} (hk : k ≤ n)
    (ask : List (Fin D → Bool) → Fin n) (past rows : List (Fin D → Bool))
    (hpos : ∃ z ∈ {z | vectorRowAnswers ask (fun j => observedPositiveColumn (z j)) past rows.length = rows},
      z ∈ (hiddenColumnTableLaw n D k hk).support) :
    ∀ j, (hiddenCompatibleSamples ask past rows j : Finset (HiddenColumnSample n k)).Nonempty := by
  obtain ⟨z, hz, hsupport⟩ := hpos
  intro j
  exact ⟨z j, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    (vectorRowAnswers_eq_iff ask _ past rows).mp hz j⟩⟩

/-- Hidden signs as well as columns are conditionally independent after a
full adaptive transcript: the latent posterior is an actual Cartesian law. -/
theorem hiddenColumnTableLaw_condition_history {n D k : ℕ} (hk : k ≤ n)
    (ask : List (Fin D → Bool) → Fin n) (past rows : List (Fin D → Bool))
    (hpos : ∃ z ∈ {z | vectorRowAnswers ask (fun j => observedPositiveColumn (z j)) past rows.length = rows},
      z ∈ (hiddenColumnTableLaw n D k hk).support) :
    (hiddenColumnTableLaw n D k hk).filter
      {z | vectorRowAnswers ask (fun j => observedPositiveColumn (z j)) past rows.length = rows} hpos =
      uniformPi (fun j => (hiddenCompatibleSamples ask past rows j : Finset (HiddenColumnSample n k)))
        (hiddenColumnTableLaw_history_feasible hk ask past rows hpos) := by
  classical
  letI := fixedColumn_nonempty hk
  let A : Fin D → Set (HiddenColumnSample n k) := fun j =>
    {z | compatibleColumn (vectorPositiveLabels ask past rows j) (vectorNegativeLabels ask past rows j)
      (observedPositiveColumn z)}
  have hset : {z : Fin D → HiddenColumnSample n k |
      vectorRowAnswers ask (fun j => observedPositiveColumn (z j)) past rows.length = rows} =
      {z | ∀ j, z j ∈ A j} := by
    ext z
    exact vectorRowAnswers_eq_iff ask _ past rows
  have hpos' : ∃ z ∈ {z | ∀ j, z j ∈ A j}, z ∈ (hiddenColumnTableLaw n D k hk).support := by
    rwa [← hset]
  have hA := hiddenColumnTableLaw_history_feasible hk ask past rows hpos
  convert uniformPi_condition_rect (fun _ : Fin D => (Finset.univ : Finset (HiddenColumnSample n k)))
    (fun _ => Finset.univ_nonempty) A hA hpos' using 1
  congr 1

/-- The posterior product formula applies to the original hard-table law,
not just to an auxiliary independently sampled model. -/
theorem fixedTableLaw_condition_history {n D k : ℕ} (hk : k ≤ n)
    (ask : List (Fin D → Bool) → Fin n) (past rows : List (Fin D → Bool))
    (hpos : ∃ ω ∈ {ω | vectorRowAnswers ask
      (fun j => observedPositiveColumn (tableColumnEquiv n D k ω j)) past rows.length = rows},
      ω ∈ (fixedTableLaw n D k hk).support) :
    ∃ hA : ∀ j, (hiddenCompatibleSamples ask past rows j : Finset (HiddenColumnSample n k)).Nonempty,
    ((fixedTableLaw n D k hk).filter {ω | vectorRowAnswers ask
      (fun j => observedPositiveColumn (tableColumnEquiv n D k ω j)) past rows.length = rows} hpos).map
      (tableColumnEquiv n D k) = uniformPi (fun j => hiddenCompatibleSamples ask past rows j) hA := by
  let A : Set (Fin D → HiddenColumnSample n k) :=
    {z | vectorRowAnswers ask (fun j => observedPositiveColumn (z j)) past rows.length = rows}
  have hpre : ∃ ω ∈ (tableColumnEquiv n D k) ⁻¹' A, ω ∈ (fixedTableLaw n D k hk).support := hpos
  have hmap : ∃ z ∈ A, z ∈ ((fixedTableLaw n D k hk).map (tableColumnEquiv n D k)).support := by
    obtain ⟨ω, hω, hs⟩ := hpos
    exact ⟨tableColumnEquiv n D k ω, hω, (PMF.mem_support_map_iff _ _ _).mpr ⟨ω, hs, rfl⟩⟩
  have hlatent : ∃ z ∈ A, z ∈ (hiddenColumnTableLaw n D k hk).support := by
    rwa [fixedTableLaw_columns] at hmap
  refine ⟨hiddenColumnTableLaw_history_feasible hk ask past rows hlatent, ?_⟩
  calc
    _ = (((fixedTableLaw n D k hk).map (tableColumnEquiv n D k)).filter A hmap) :=
      map_filter_preimage _ _ _ hpre hmap
    _ = (hiddenColumnTableLaw n D k hk).filter A hlatent := by congr 1; exact fixedTableLaw_columns n D k hk
    _ = _ := hiddenColumnTableLaw_condition_history hk ask past rows hlatent

end FullJet
