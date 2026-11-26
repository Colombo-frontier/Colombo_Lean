import NCConcave16991.ConditionalHaarStopping

/-!
# Causal adaptive column revelation and actual stopping-state measurability

A measurable state machine chooses the next column using its current state,
then updates from that actual column. For a proposed final revealed set A,
run the same machine against the oracle with every other column replaced by
zero. On the event that the final revealed set is A, the two complete runs
agree. Conversely the masked run has final set A exactly on that event.
Consequently the event is measurable from the actually revealed columns A.
-/

open Set MeasureTheory
open scoped BigOperators

namespace NCConcave16991.Haar.ColumnReveal

noncomputable section

variable {k : ℕ} {S : Type*}

def run (read : S → Fin k) (update : S → EuclideanSpace ℝ (Fin k) → S)
    (initial : S) (oracle : Fin k → EuclideanSpace ℝ (Fin k)) : ℕ → S
  | 0 => initial
  | t + 1 => update (run read update initial oracle t)
      (oracle (read (run read update initial oracle t)))

def support (read : S → Fin k) (update : S → EuclideanSpace ℝ (Fin k) → S)
    (initial : S) (oracle : Fin k → EuclideanSpace ℝ (Fin k)) (budget : ℕ) : Finset (Fin k) :=
  Finset.univ.image (fun t : Fin budget ↦ read (run read update initial oracle t.val))

theorem read_mem_support (read : S → Fin k) (update : S → EuclideanSpace ℝ (Fin k) → S)
    (initial : S) (oracle : Fin k → EuclideanSpace ℝ (Fin k)) {t budget : ℕ} (ht : t < budget) :
    read (run read update initial oracle t) ∈ support read update initial oracle budget := by
  exact Finset.mem_image.mpr ⟨⟨t, ht⟩, Finset.mem_univ _, rfl⟩

theorem run_prefix_eq_of_agree_on_support (read : S → Fin k)
    (update : S → EuclideanSpace ℝ (Fin k) → S) (initial : S)
    (oracle other : Fin k → EuclideanSpace ℝ (Fin k)) (budget : ℕ)
    (hagrees : ∀ i ∈ support read update initial oracle budget, oracle i = other i) :
    ∀ t ≤ budget, run read update initial oracle t = run read update initial other t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro ht
    change update (run read update initial oracle t) (oracle (read (run read update initial oracle t))) =
      update (run read update initial other t) (other (read (run read update initial other t)))
    rw [← ih (by omega)]
    rw [hagrees _ (read_mem_support read update initial oracle (by omega : t < budget))]

theorem support_eq_of_agree_on_support (read : S → Fin k)
    (update : S → EuclideanSpace ℝ (Fin k) → S) (initial : S)
    (oracle other : Fin k → EuclideanSpace ℝ (Fin k)) (budget : ℕ)
    (hagrees : ∀ i ∈ support read update initial oracle budget, oracle i = other i) :
    support read update initial oracle budget = support read update initial other budget := by
  unfold support
  congr 1
  funext t
  rw [run_prefix_eq_of_agree_on_support read update initial oracle other budget hagrees t.val (by omega)]

def columnOracle (Q : OrthogonalGroup k) (i : Fin k) : EuclideanSpace ℝ (Fin k) :=
  orthogonalLinearIsometryEquiv Q (basisVector i)

def maskedColumn (A : Finset (Fin k)) (Q : OrthogonalGroup k) (i : Fin k) : EuclideanSpace ℝ (Fin k) :=
  if i ∈ A then columnOracle Q i else 0

theorem maskedColumn_eq_of_mem (A : Finset (Fin k)) (Q : OrthogonalGroup k) (i : Fin k) (hi : i ∈ A) :
    maskedColumn A Q i = columnOracle Q i := if_pos hi

theorem maskedColumn_observed (A : Finset (Fin k)) (i : Fin k) :
    StronglyMeasurable[columnSigma A] (fun Q ↦ maskedColumn A Q i) := by
  letI : MeasurableSpace (OrthogonalGroup k) := columnSigma A
  by_cases hi : i ∈ A
  · have hobs : Measurable[columnSigma A] (observeColumns A) := measurable_iff_comap_le.mpr le_rfl
    have hm := (measurable_pi_iff.mp hobs) (⟨i,hi⟩ : A)
    simpa only [maskedColumn, if_pos hi, columnOracle, observeColumns] using hm.stronglyMeasurable
  · simpa only [maskedColumn, if_neg hi] using
      (stronglyMeasurable_const : StronglyMeasurable[columnSigma A] (fun _ : OrthogonalGroup k ↦
        (0 : EuclideanSpace ℝ (Fin k))))

theorem maskedColumn_selected_observed (A : Finset (Fin k))
    (i : OrthogonalGroup k → Fin k) (hi : Measurable[columnSigma A] i) :
    Measurable[columnSigma A] (fun Q ↦ maskedColumn A Q (i Q)) := by
  have hterm (j : Fin k) : StronglyMeasurable[columnSigma A]
      ({Q | i Q = j}.indicator (fun Q ↦ maskedColumn A Q j)) :=
    (maskedColumn_observed A j).indicator (hi (measurableSet_singleton j))
  have hsum := Finset.stronglyMeasurable_fun_sum Finset.univ (fun j _ ↦ hterm j)
  have he : (fun Q ↦ ∑ j : Fin k, {Q | i Q = j}.indicator (fun Q ↦ maskedColumn A Q j) Q) =
      fun Q ↦ maskedColumn A Q (i Q) := by
    funext Q
    calc
      _ = {Q | i Q = i Q}.indicator (fun Q ↦ maskedColumn A Q (i Q)) Q := by
        apply Finset.sum_eq_single (i Q)
        · intro j hj hji
          exact indicator_of_notMem (by simpa only [mem_ofPred_eq] using Ne.symm hji) _
        · simp
      _ = _ := indicator_of_mem rfl _
  rw [he] at hsum
  exact hsum.measurable

theorem masked_run_measurable [MeasurableSpace S]
    (read : S → Fin k) (hread : Measurable read)
    (update : S → EuclideanSpace ℝ (Fin k) → S) (hupdate : Measurable (Function.uncurry update))
    (initial : S) (A : Finset (Fin k)) (t : ℕ) :
    Measurable[columnSigma A] (fun Q ↦ run read update initial (maskedColumn A Q) t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    change Measurable[columnSigma A] (fun Q ↦ update
      (run read update initial (maskedColumn A Q) t)
      (maskedColumn A Q (read (run read update initial (maskedColumn A Q) t))))
    exact hupdate.comp (ih.prodMk (maskedColumn_selected_observed A _ (hread.comp ih)))

theorem masked_support_fiber_measurable [MeasurableSpace S]
    (read : S → Fin k) (hread : Measurable read)
    (update : S → EuclideanSpace ℝ (Fin k) → S) (hupdate : Measurable (Function.uncurry update))
    (initial : S) (A : Finset (Fin k)) (budget : ℕ) :
    MeasurableSet[columnSigma A] {Q | support read update initial (maskedColumn A Q) budget = A} := by
  letI : MeasurableSpace (OrthogonalGroup k) := columnSigma A
  have hm : Measurable[columnSigma A] (fun Q ↦ fun t : Fin budget ↦
      read (run read update initial (maskedColumn A Q) t.val)) :=
    measurable_pi_iff.mpr (fun t ↦ hread.comp (masked_run_measurable read hread update hupdate initial A t.val))
  have hs : MeasurableSet {v : Fin budget → Fin k | Finset.univ.image v = A} :=
    ({v : Fin budget → Fin k | Finset.univ.image v = A} : Set (Fin budget → Fin k)).to_countable.measurableSet
  exact hm hs

theorem support_eq_iff_masked_support_eq (read : S → Fin k)
    (update : S → EuclideanSpace ℝ (Fin k) → S) (initial : S)
    (A : Finset (Fin k)) (Q : OrthogonalGroup k) (budget : ℕ) :
    support read update initial (columnOracle Q) budget = A ↔
      support read update initial (maskedColumn A Q) budget = A := by
  constructor
  · intro hA
    have he := support_eq_of_agree_on_support read update initial (columnOracle Q) (maskedColumn A Q) budget
      (fun i hi ↦ (maskedColumn_eq_of_mem A Q i (hA ▸ hi)).symm)
    exact he.symm.trans hA
  · intro hA
    have he := support_eq_of_agree_on_support read update initial (maskedColumn A Q) (columnOracle Q) budget
      (fun i hi ↦ maskedColumn_eq_of_mem A Q i (hA ▸ hi))
    exact he.symm.trans hA

/-- Causality discharges the stopping-state measurability condition: the
actual final revealed-set event is determined by those actual columns. -/
theorem support_fiber_measurable [MeasurableSpace S]
    (read : S → Fin k) (hread : Measurable read)
    (update : S → EuclideanSpace ℝ (Fin k) → S) (hupdate : Measurable (Function.uncurry update))
    (initial : S) (A : Finset (Fin k)) (budget : ℕ) :
    MeasurableSet[columnSigma A] {Q | support read update initial (columnOracle Q) budget = A} := by
  have he : {Q : OrthogonalGroup k | support read update initial (columnOracle Q) budget = A} =
      {Q | support read update initial (maskedColumn A Q) budget = A} :=
    Set.ext (fun Q ↦ support_eq_iff_masked_support_eq read update initial A Q budget)
  rw [he]
  exact masked_support_fiber_measurable read hread update hupdate initial A budget

theorem run_eq_masked_on_support_fiber (read : S → Fin k)
    (update : S → EuclideanSpace ℝ (Fin k) → S) (initial : S)
    (A : Finset (Fin k)) (Q : OrthogonalGroup k) (budget : ℕ)
    (hA : support read update initial (columnOracle Q) budget = A) :
    run read update initial (columnOracle Q) budget =
      run read update initial (maskedColumn A Q) budget :=
  run_prefix_eq_of_agree_on_support read update initial (columnOracle Q) (maskedColumn A Q) budget
    (fun i hi ↦ (maskedColumn_eq_of_mem A Q i (hA ▸ hi)).symm) budget le_rfl

end

end NCConcave16991.Haar.ColumnReveal
