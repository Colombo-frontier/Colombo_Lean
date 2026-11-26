import SampleReuse.PersistentTableLaw

/-! Exact lazy-draw equivalence when the table law depends on a hidden
initial parameter. The parameter is retained in the transcript. -/

open SecondOrder
open scoped Classical ENNReal BigOperators
namespace SampleReuse
noncomputable section
variable {S Key A : Type} [Fintype S] [Fintype Key] [Fintype A]

theorem finite_pmf_bind_mean {B C : Type*} [Fintype B] [Fintype C]
    (p : PMF B) (q : B → PMF C) (F : C → ℝ) :
    pmfMean (p.bind q) F = pmfMean p (fun b => pmfMean (q b) F) := by
  simp only [pmfMean, smul_eq_mul, finite_pmf_bind_toReal, Finset.sum_mul,
    Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

omit [Fintype S] [Fintype Key] [Fintype A] in
theorem tableHistory_initial (query : ∀ n, FiniteHistory S A n → Key)
    (s : S) (table : Key → A) : ∀ n, finiteHistoryInitial n (tableHistory query s table n) = s := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => exact ih

def seededDisclosurePMF (query : ∀ n, FiniteHistory S A n → Key) (p : S → Key → PMF A)
    (n : ℕ) (h : FiniteHistory S A n) : PMF A :=
  disclosurePMF (disclosureCache query n h (query n h)) (p (finiteHistoryInitial n h) (query n h))

def seededTablePMF (ν : PMF S) (p : S → Key → PMF A) : PMF (S × (Key → A)) :=
  finiteConditionalPMF ν (fun s => finitePiPMF (p s))

theorem tableHistory_mean_succ (query : ∀ n, FiniteHistory S A n → Key)
    (p : Key → PMF A) (s : S) (n : ℕ) (F : FiniteHistory S A (n + 1) → ℝ) :
    pmfMean (finitePiPMF p) (fun table => F (tableHistory query s table (n + 1))) =
      pmfMean (finitePiPMF p) (fun table =>
        pmfMean (disclosurePMF (disclosureCache query n (tableHistory query s table n)
          (query n (tableHistory query s table n))) (p (query n (tableHistory query s table n))))
          (fun a => F (tableHistory query s table n, a))) := by
  rw [← pmfMean_map (finitePiPMF p) (fun table => tableHistory query s table (n + 1)) F]
  change pmfMean (preallocatedHistoryPMF query p s (n + 1)) F = _
  rw [preallocatedHistoryPMF_succ, finite_pmf_bind_mean]
  simp_rw [pmfMean_map]
  exact pmfMean_map (finitePiPMF p) (fun table => tableHistory query s table n) _

/-- Test-function equality for the actual once-sampled table, with a
possibly biased table law conditional on the hidden seed. -/
theorem seeded_table_history_mean (ν : PMF S) (query : ∀ n, FiniteHistory S A n → Key)
    (p : S → Key → PMF A) : ∀ n (F : FiniteHistory S A n → ℝ),
    pmfMean (seededTablePMF ν p) (fun z => F (tableHistory query z.1 z.2 n)) =
      pmfMean (finiteAdaptiveLaw ν (seededDisclosurePMF query p) n) F := by
  intro n
  induction n with
  | zero =>
    intro F
    rw [seededTablePMF, finiteConditionalPMF_mean]
    simp only [tableHistory, pmfMean_const, finiteAdaptiveLaw]
  | succ n ih =>
    intro F
    rw [seededTablePMF, finiteConditionalPMF_mean]
    simp_rw [tableHistory_mean_succ]
    have ht : pmfMean ν (fun s => pmfMean (finitePiPMF (p s)) (fun table =>
        pmfMean (disclosurePMF (disclosureCache query n (tableHistory query s table n)
          (query n (tableHistory query s table n))) (p s (query n (tableHistory query s table n))))
          (fun a => F (tableHistory query s table n, a)))) =
      pmfMean (seededTablePMF ν p) (fun z =>
        pmfMean (seededDisclosurePMF query p n (tableHistory query z.1 z.2 n))
          (fun a => F (tableHistory query z.1 z.2 n, a))) := by
      rw [seededTablePMF, finiteConditionalPMF_mean]
      simp only [seededDisclosurePMF, tableHistory_initial]
    rw [ht, ih (fun h => pmfMean (seededDisclosurePMF query p n h) (fun a => F (h, a)))]
    exact (finiteConditionalPMF_mean _ _ F).symm

theorem seeded_table_history_law (ν : PMF S) (query : ∀ n, FiniteHistory S A n → Key)
    (p : S → Key → PMF A) (n : ℕ) :
    (seededTablePMF ν p).map (fun z => tableHistory query z.1 z.2 n) =
      finiteAdaptiveLaw ν (seededDisclosurePMF query p) n := by
  ext h
  apply (ENNReal.toReal_eq_toReal (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [finite_pmf_map_toReal, seeded_table_history_mean ν query p n (fun b => if b = h then 1 else 0)]
  simp [pmfMean, smul_eq_mul]

end
end SampleReuse
