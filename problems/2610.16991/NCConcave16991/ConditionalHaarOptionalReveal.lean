import NCConcave16991.ConditionalHaarReveal

/-!
# Causal revelation with steps that do not access this Haar block

For a product of hidden rotations, fix all other rotations and the private
seed. A global query may reveal one column of the selected block or may not
access it. The latter steps return the deterministic zero response. The same
actual masked-run argument proves stopping-set measurability for this model.
-/

open Set MeasureTheory
open scoped BigOperators

namespace NCConcave16991.Haar.OptionalReveal

noncomputable section

variable {k : ℕ} {S : Type*}

instance optionalIndexMeasurableSpace (k : ℕ) : MeasurableSpace (Option (Fin k)) := ⊤

instance optionalIndexMeasurableSingletonClass (k : ℕ) : MeasurableSingletonClass (Option (Fin k)) :=
  ⟨fun _ ↦ trivial⟩

def run (read : S → Option (Fin k)) (update : S → EuclideanSpace ℝ (Fin k) → S)
    (initial : S) (oracle : Fin k → EuclideanSpace ℝ (Fin k)) : ℕ → S
  | 0 => initial
  | t + 1 => update (run read update initial oracle t)
      ((read (run read update initial oracle t)).elim 0 oracle)

def support (read : S → Option (Fin k)) (update : S → EuclideanSpace ℝ (Fin k) → S)
    (initial : S) (oracle : Fin k → EuclideanSpace ℝ (Fin k)) (budget : ℕ) : Finset (Fin k) :=
  Finset.univ.biUnion (fun t : Fin budget ↦ (read (run read update initial oracle t.val)).toFinset)

theorem read_mem_support (read : S → Option (Fin k)) (update : S → EuclideanSpace ℝ (Fin k) → S)
    (initial : S) (oracle : Fin k → EuclideanSpace ℝ (Fin k)) {t budget : ℕ} (ht : t < budget)
    {i : Fin k} (hi : read (run read update initial oracle t) = some i) :
    i ∈ support read update initial oracle budget := by
  apply Finset.mem_biUnion.mpr
  refine ⟨⟨t,ht⟩, Finset.mem_univ _, ?_⟩
  simp [hi]

theorem run_prefix_eq_of_agree_on_support (read : S → Option (Fin k))
    (update : S → EuclideanSpace ℝ (Fin k) → S) (initial : S)
    (oracle other : Fin k → EuclideanSpace ℝ (Fin k)) (budget : ℕ)
    (hagrees : ∀ i ∈ support read update initial oracle budget, oracle i = other i) :
    ∀ t ≤ budget, run read update initial oracle t = run read update initial other t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro ht
    change update (run read update initial oracle t)
        ((read (run read update initial oracle t)).elim 0 oracle) =
      update (run read update initial other t) ((read (run read update initial other t)).elim 0 other)
    rw [← ih (by omega)]
    cases hr : read (run read update initial oracle t) with
    | none => rfl
    | some i =>
      simp only [Option.elim_some]
      rw [hagrees i (read_mem_support read update initial oracle (by omega : t < budget) hr)]

theorem support_eq_of_agree_on_support (read : S → Option (Fin k))
    (update : S → EuclideanSpace ℝ (Fin k) → S) (initial : S)
    (oracle other : Fin k → EuclideanSpace ℝ (Fin k)) (budget : ℕ)
    (hagrees : ∀ i ∈ support read update initial oracle budget, oracle i = other i) :
    support read update initial oracle budget = support read update initial other budget := by
  unfold support
  congr 1
  funext t
  rw [run_prefix_eq_of_agree_on_support read update initial oracle other budget hagrees t.val (by omega)]

theorem support_card_le (read : S → Option (Fin k)) (update : S → EuclideanSpace ℝ (Fin k) → S)
    (initial : S) (oracle : Fin k → EuclideanSpace ℝ (Fin k)) (budget : ℕ) :
    (support read update initial oracle budget).card ≤ budget := by
  apply Finset.card_biUnion_le.trans
  calc
    _ ≤ ∑ _t : Fin budget, (1 : ℕ) := by
      apply Finset.sum_le_sum
      intro t ht
      cases read (run read update initial oracle t.val) <;> simp
    _ = _ := by simp

theorem maskedColumn_selected_observed (A : Finset (Fin k))
    (i : OrthogonalGroup k → Option (Fin k)) (hi : Measurable[columnSigma A] i) :
    Measurable[columnSigma A] (fun Q ↦ (i Q).elim 0 (ColumnReveal.maskedColumn A Q)) := by
  have hterm (j : Fin k) : StronglyMeasurable[columnSigma A]
      ({Q | i Q = some j}.indicator (fun Q ↦ ColumnReveal.maskedColumn A Q j)) :=
    (ColumnReveal.maskedColumn_observed A j).indicator (hi (measurableSet_singleton (some j)))
  have hsum := Finset.stronglyMeasurable_fun_sum Finset.univ (fun j _ ↦ hterm j)
  have he : (fun Q ↦ ∑ j : Fin k, {Q | i Q = some j}.indicator
      (fun Q ↦ ColumnReveal.maskedColumn A Q j) Q) =
      fun Q ↦ (i Q).elim 0 (ColumnReveal.maskedColumn A Q) := by
    funext Q
    cases hQ : i Q with
    | none => simp [hQ]
    | some l =>
      calc
        _ = {Q | i Q = some l}.indicator (fun Q ↦ ColumnReveal.maskedColumn A Q l) Q := by
          apply Finset.sum_eq_single l
          · intro j hj hjl
            apply indicator_of_notMem
            simpa only [mem_ofPred_eq, hQ, Option.some.injEq] using Ne.symm hjl
          · simp
        _ = _ := by
          rw [indicator_of_mem (show Q ∈ {Q | i Q = some l} from hQ)]
          rfl
  rw [he] at hsum
  exact hsum.measurable

theorem masked_run_measurable [MeasurableSpace S]
    (read : S → Option (Fin k)) (hread : Measurable read)
    (update : S → EuclideanSpace ℝ (Fin k) → S) (hupdate : Measurable (Function.uncurry update))
    (initial : S) (A : Finset (Fin k)) (t : ℕ) :
    Measurable[columnSigma A] (fun Q ↦ run read update initial (ColumnReveal.maskedColumn A Q) t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    exact hupdate.comp (ih.prodMk (maskedColumn_selected_observed A _ (hread.comp ih)))

theorem masked_support_fiber_measurable [MeasurableSpace S]
    (read : S → Option (Fin k)) (hread : Measurable read)
    (update : S → EuclideanSpace ℝ (Fin k) → S) (hupdate : Measurable (Function.uncurry update))
    (initial : S) (A : Finset (Fin k)) (budget : ℕ) :
    MeasurableSet[columnSigma A]
      {Q | support read update initial (ColumnReveal.maskedColumn A Q) budget = A} := by
  letI : MeasurableSpace (OrthogonalGroup k) := columnSigma A
  have hm : Measurable[columnSigma A] (fun Q ↦ fun t : Fin budget ↦
      read (run read update initial (ColumnReveal.maskedColumn A Q) t.val)) :=
    measurable_pi_iff.mpr (fun t ↦ hread.comp (masked_run_measurable read hread update hupdate initial A t.val))
  have hs : MeasurableSet {v : Fin budget → Option (Fin k) |
      Finset.univ.biUnion (fun t ↦ (v t).toFinset) = A} :=
    ({v : Fin budget → Option (Fin k) | Finset.univ.biUnion (fun t ↦ (v t).toFinset) = A} :
      Set (Fin budget → Option (Fin k))).to_countable.measurableSet
  exact hm hs

theorem support_eq_iff_masked_support_eq (read : S → Option (Fin k))
    (update : S → EuclideanSpace ℝ (Fin k) → S) (initial : S)
    (A : Finset (Fin k)) (Q : OrthogonalGroup k) (budget : ℕ) :
    support read update initial (ColumnReveal.columnOracle Q) budget = A ↔
      support read update initial (ColumnReveal.maskedColumn A Q) budget = A := by
  constructor
  · intro hA
    have he := support_eq_of_agree_on_support read update initial
      (ColumnReveal.columnOracle Q) (ColumnReveal.maskedColumn A Q) budget
      (fun i hi ↦ (ColumnReveal.maskedColumn_eq_of_mem A Q i (hA ▸ hi)).symm)
    exact he.symm.trans hA
  · intro hA
    have he := support_eq_of_agree_on_support read update initial
      (ColumnReveal.maskedColumn A Q) (ColumnReveal.columnOracle Q) budget
      (fun i hi ↦ ColumnReveal.maskedColumn_eq_of_mem A Q i (hA ▸ hi))
    exact he.symm.trans hA

theorem support_fiber_measurable [MeasurableSpace S]
    (read : S → Option (Fin k)) (hread : Measurable read)
    (update : S → EuclideanSpace ℝ (Fin k) → S) (hupdate : Measurable (Function.uncurry update))
    (initial : S) (A : Finset (Fin k)) (budget : ℕ) :
    MeasurableSet[columnSigma A]
      {Q | support read update initial (ColumnReveal.columnOracle Q) budget = A} := by
  have he : {Q : OrthogonalGroup k | support read update initial (ColumnReveal.columnOracle Q) budget = A} =
      {Q | support read update initial (ColumnReveal.maskedColumn A Q) budget = A} :=
    Set.ext (fun Q ↦ support_eq_iff_masked_support_eq read update initial A Q budget)
  rw [he]
  exact masked_support_fiber_measurable read hread update hupdate initial A budget

theorem run_eq_masked_on_support_fiber (read : S → Option (Fin k))
    (update : S → EuclideanSpace ℝ (Fin k) → S) (initial : S)
    (A : Finset (Fin k)) (Q : OrthogonalGroup k) (budget : ℕ)
    (hA : support read update initial (ColumnReveal.columnOracle Q) budget = A) :
    run read update initial (ColumnReveal.columnOracle Q) budget =
      run read update initial (ColumnReveal.maskedColumn A Q) budget :=
  run_prefix_eq_of_agree_on_support read update initial (ColumnReveal.columnOracle Q)
    (ColumnReveal.maskedColumn A Q) budget
    (fun i hi ↦ (ColumnReveal.maskedColumn_eq_of_mem A Q i (hA ▸ hi)).symm) budget le_rfl

end

end NCConcave16991.Haar.OptionalReveal
