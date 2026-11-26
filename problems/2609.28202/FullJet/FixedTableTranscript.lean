import FullJet.RowAlignment
import FullJet.TablePosterior

open scoped BigOperators InnerProductSpace

namespace FullJet

theorem pmf_map_mass_toReal {α β : Type*} [Fintype α] [DecidableEq β] (p : PMF α) (f : α → β) (b : β) :
    ((p.map f) b).toReal = ∑ x, if f x = b then (p x).toReal else 0 := by
  classical
  rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply, pmf_event_toReal]
  simp

theorem uniform_product_mass {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (a : α) (b : β) :
    ((PMF.uniformOfFintype (α × β)) (a, b)).toReal =
      ((PMF.uniformOfFintype α) a).toReal * ((PMF.uniformOfFintype β) b).toReal := by
  simp [PMF.uniformOfFintype_apply, Fintype.card_prod, ENNReal.mul_inv, ENNReal.toReal_mul]

theorem uniform_pair_map_mass {α β γ : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (f : α → β → γ) (a : α) (c : γ) :
    (((PMF.uniformOfFintype (α × β)).map (fun z => (z.1, f z.1 z.2))) (a, c)).toReal =
      ((PMF.uniformOfFintype α) a).toReal *
        (((PMF.uniformOfFintype β).map (f a)) c).toReal := by
  classical
  rw [pmf_map_mass_toReal, Fintype.sum_prod_type]
  simp only [Prod.mk.injEq, uniform_product_mass]
  rw [Finset.sum_eq_single a]
  · simp only [true_and]
    rw [pmf_map_mass_toReal, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    split_ifs <;> simp
  · intro a' ha' hne
    simp [hne]
  · simp

theorem uniform_cube_mass (D : ℕ) (theta : Fin D → Bool) :
    ((PMF.uniformOfFintype (Fin D → Bool)) theta).toReal = cubeWeight theta := by
  rw [cubeWeight_eq]
  simp [PMF.uniformOfFintype_apply, Fintype.card_fun, one_div, inv_pow]

theorem uniformPi_mass {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (s : ι → Finset α) (hs : ∀ j, (s j).Nonempty) (x : ι → α) :
    ((uniformPi s hs) x).toReal = ∏ j, ((PMF.uniformOfFinset (s j) (hs j)) (x j)).toReal := by
  have h := uniformPi_map_coordinates s hs (fun _ => id) x
  simpa only [show (fun (x : ι → α) j => id (x j)) = id from rfl, PMF.map_id] using h

def fixedObservedColumns {n D k : ℕ} (theta : Fin D → Bool) (S : Fin D → FixedColumn n k) :
    Fin D → Finset (Fin n) := fun j => if theta j then (S j).val else (S j).valᶜ

/-- Fixing the hidden signs in the original sample gives exactly the signed
fixed-size column law used in the information estimate. -/
theorem fixedObservedColumns_law (n D k : ℕ) (hk : k ≤ n) (theta : Fin D → Bool) :
    letI := fixedColumn_nonempty hk
    (PMF.uniformOfFintype (Fin D → FixedColumn n k)).map (fixedObservedColumns theta) =
      vectorColumnLaw Finset.univ (signedColumnCount (n := n) k theta)
        (fun j => by simpa using signedColumnCount_le k hk theta j) := by
  classical
  letI := fixedColumn_nonempty hk
  have hunif : PMF.uniformOfFintype (Fin D → FixedColumn n k) =
      uniformPi (fun _ : Fin D => (Finset.univ : Finset (FixedColumn n k)))
        (fun _ => Finset.univ_nonempty) := by
    simp [PMF.uniformOfFintype, uniformPi, Fintype.piFinset_univ]
  ext S
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [hunif]
  unfold fixedObservedColumns
  rw [uniformPi_map_coordinates (fun _ : Fin D => (Finset.univ : Finset (FixedColumn n k)))
    (fun _ => Finset.univ_nonempty) (fun j T => if theta j then T.val else T.valᶜ) S]
  unfold vectorColumnLaw
  rw [uniformPi_mass]
  apply Finset.prod_congr rfl
  intro j hj
  change (((fixedColumnLaw n k hk).map (fun T => if theta j then T.val else T.valᶜ)) (S j)).toReal = _
  cases hb : theta j
  · simp only [hb, Bool.false_eq_true, if_false, fixedColumnLaw_negated, signedColumnCount]
    rfl
  · simp only [hb, if_true, fixedColumnLaw_forget, signedColumnCount]
    rfl

def fixedTableTranscript {n D k : ℕ} (ask : List (Fin D → Bool) → Fin n)
    (past : List (Fin D → Bool)) (q : ℕ) (ω : FixedTableSample n D k) :
    (Fin D → Bool) × (Fin q → Fin D → Bool) :=
  (ω.1, runReplies (fun S hist j => decide (ask hist ∈ S j))
    (fixedObservedColumns ω.1 ω.2) past q)

/-- Exact joint mass for the original hard table: the hidden signs and full
adaptive transcript have the already analyzed joint distribution. -/
theorem fixedTableTranscript_mass {n D k : ℕ} (hk : k ≤ n)
    (ask : List (Fin D → Bool) → Fin n) (past : List (Fin D → Bool)) (q : ℕ)
    (z : (Fin D → Bool) × (Fin q → Fin D → Bool)) :
    (((fixedTableLaw n D k hk).map (fixedTableTranscript ask past q)) z).toReal =
      rowJointWeight k hk ask past q z := by
  classical
  letI := fixedColumn_nonempty hk
  obtain ⟨theta, v⟩ := z
  unfold fixedTableLaw fixedTableTranscript
  rw [uniform_pair_map_mass (fun theta (S : Fin D → FixedColumn n k) =>
    runReplies (fun S hist j => decide (ask hist ∈ S j)) (fixedObservedColumns theta S) past q)
      theta v, uniform_cube_mass]
  unfold rowJointWeight signedRowTranscriptWeight signedRowTranscriptLaw
  congr 2
  have hcomp := PMF.map_comp (fixedObservedColumns theta)
    (PMF.uniformOfFintype (Fin D → FixedColumn n k))
    (fun S => runReplies (fun S hist j => decide (ask hist ∈ S j)) S past q)
  rw [fixedObservedColumns_law n D k hk theta] at hcomp
  exact congrArg (fun μ : PMF (Fin q → Fin D → Bool) => μ v) hcomp.symm

theorem fixedObservedColumns_sign {n D k : ℕ} (ω : FixedTableSample n D k) (j : Fin D) (i : Fin n) :
    columnSign (fixedObservedColumns ω.1 ω.2 j) i =
      rareSign (ω.1 j) * columnSign (ω.2 j).val i := by
  exact observedPositiveColumn_sign ω j i

theorem fixedTable_alignment_probability_eq {n D k : ℕ} {κ : Type*} [Fintype κ]
    (hk : k ≤ n) (ask : List (Fin D → Bool) → Fin n) (past : List (Fin D → Bool)) (q : ℕ)
    (w : (Fin q → Fin D → Bool) → κ → EuclideanSpace ℝ (Fin D)) (a : ℝ) :
    ((fixedTableLaw n D k hk).toOuterMeasure {ω |
      ∃ l, a ≤ ⟪sampledDirection ω, w (fixedTableTranscript ask past q ω).2 l⟫_ℝ}).toReal =
    ∑ z ∈ Finset.univ.filter (fun z : (Fin D → Bool) × (Fin q → Fin D → Bool) =>
      ∃ l, a ≤ ⟪normalizedVector (fun j => rareSign (z.1 j)), w z.2 l⟫_ℝ), rowJointWeight k hk ask past q z := by
  classical
  let A : Set ((Fin D → Bool) × (Fin q → Fin D → Bool)) := {z |
    ∃ l, a ≤ ⟪normalizedVector (fun j => rareSign (z.1 j)), w z.2 l⟫_ℝ}
  change ((fixedTableLaw n D k hk).toOuterMeasure ((fixedTableTranscript ask past q) ⁻¹' A)).toReal = _
  rw [← PMF.toOuterMeasure_map_apply, pmf_event_toReal]
  simp_rw [fixedTableTranscript_mass, Finset.sum_filter]
  rfl

/-- The row-cost estimate applies to the very same hard-table sample used
to construct the objective function and its normalized hidden direction. -/
theorem fixedTable_row_cost_lower {n D k : ℕ} {κ : Type*} [Fintype κ]
    (hn : 0 < n) (hD : 0 < D) (hk : k ≤ n)
    (m : ℝ) (hm : 0 < m) (hmn : m ≤ (n : ℝ) / 16)
    (hbalance : 2 * (k : ℝ) = n + m)
    (ask : List (Fin D → Bool) → Fin n) (past : List (Fin D → Bool)) (q : ℕ)
    (w : (Fin q → Fin D → Bool) → κ → EuclideanSpace ℝ (Fin D))
    (hw : ∀ v l, ‖w v l‖ ≤ 1) (a : ℝ) (ha : 0 < a)
    (hdim : 32 * Real.log 2 ≤ a ^ 2 * D)
    (hfamily : (Fintype.card κ : ℝ) ≤ Real.exp (a ^ 2 * D / 4))
    (hsuccess : 1 / 2 ≤ ((fixedTableLaw n D k hk).toOuterMeasure {ω |
      ∃ l, a ≤ ⟪sampledDirection ω, w (fixedTableTranscript ask past q ω).2 l⟫_ℝ}).toReal) :
    min ((n : ℝ) / 18) (a ^ 2 / (1024 * (m / n) ^ 2)) < q := by
  rw [fixedTable_alignment_probability_eq] at hsuccess
  exact adaptive_row_cost_lower hn hD k hk m hm hmn hbalance ask past q w hw a ha hdim hfamily hsuccess

end FullJet
