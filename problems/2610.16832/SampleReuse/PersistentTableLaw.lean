import SampleReuse.PersistentTableHistory

/-! Exact equivalence between preallocated product tables and lazy cache draws. -/

open SecondOrder
open scoped Classical ENNReal BigOperators
namespace SampleReuse
noncomputable section
variable {S Key A : Type} [Fintype Key] [Fintype A]

theorem tableHistory_disclosure_mean
    (query : ∀ n, FiniteHistory S A n → Key) (p : Key → PMF A) (s : S)
    (n : ℕ) (h : FiniteHistory S A n) (F : A → ℝ) :
    pmfMean (finitePiPMF p) (fun table => if tableHistory query s table n = h then F (table (query n h)) else 0) =
      pmfMean (finitePiPMF p) (fun table => if tableHistory query s table n = h then
        pmfMean (disclosurePMF (disclosureCache query n h (query n h)) (p (query n h))) F else 0) := by
  cases hc : disclosureCache query n h (query n h) with
  | none =>
    simpa only [hc, disclosurePMF] using tableHistory_fresh_coordinate_mean query p s n h (query n h) hc F
  | some a =>
    apply pmfMean_congr
    intro table
    by_cases hh : tableHistory query s table n = h
    · have hcache : disclosureCache query n (tableHistory query s table n) (query n h) = some a := by
        rw [hh]
        exact hc
      have ha := tableHistory_cache_consistent query s table n (query n h) a hcache
      simp [hh, hc, disclosurePMF, ha, pmfMean, apply_ite ENNReal.toReal]
    · simp only [if_neg hh]

theorem finite_pmf_map_toReal {B C : Type*} [Fintype B]
    (p : PMF B) (f : B → C) (c : C) :
    (p.map f c).toReal = pmfMean p (fun b => if f b = c then 1 else 0) := by
  rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum]
  · simp only [pmfMean, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hb : f b = c
    · simp [hb]
    · simp only [if_neg hb, if_neg (Ne.symm hb), ENNReal.toReal_zero, mul_zero]
  · intro b _
    split_ifs <;> simp [p.apply_ne_top]

theorem finite_pmf_bind_toReal {B C : Type*} [Fintype B]
    (p : PMF B) (q : B → PMF C) (c : C) :
    (p.bind q c).toReal = pmfMean p (fun b => (q b c).toReal) := by
  rw [PMF.bind_apply, tsum_fintype, ENNReal.toReal_sum]
  · simp only [ENNReal.toReal_mul, pmfMean, smul_eq_mul]
  · intro b _
    exact ENNReal.mul_ne_top (p.apply_ne_top _) ((q b).apply_ne_top _)

def preallocatedHistoryPMF (query : ∀ n, FiniteHistory S A n → Key)
    (p : Key → PMF A) (s : S) (n : ℕ) : PMF (FiniteHistory S A n) :=
  (finitePiPMF p).map (fun table => tableHistory query s table n)

/-- Actual fixed-table transcript law has exactly the lazy cache transition.
This holds for each private seed separately, so the seed type and seed law
need not be finite. -/
theorem preallocatedHistoryPMF_succ (query : ∀ n, FiniteHistory S A n → Key)
    (p : Key → PMF A) (s : S) (n : ℕ) :
    preallocatedHistoryPMF query p s (n + 1) =
      (preallocatedHistoryPMF query p s n).bind (fun h =>
        (disclosurePMF (disclosureCache query n h (query n h)) (p (query n h))).map (fun a => (h, a))) := by
  unfold preallocatedHistoryPMF
  rw [PMF.bind_map]
  ext ha
  rcases ha with ⟨h, a₀⟩
  apply (ENNReal.toReal_eq_toReal (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [finite_pmf_map_toReal, finite_pmf_bind_toReal]
  simp only [Function.comp_apply, finite_pmf_map_toReal]
  have hh := tableHistory_disclosure_mean query p s n h (fun a => if a = a₀ then 1 else 0)
  have hp (x y : FiniteHistory S A n) (a b : A) :
      ((x, a) : FiniteHistory S A (n + 1)) = (y, b) ↔ x = y ∧ a = b :=
    ⟨fun h => ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩, fun h => Prod.ext h.1 h.2⟩
  calc
    _ = pmfMean (finitePiPMF p) (fun table => if tableHistory query s table n = h then
        (if table (query n h) = a₀ then 1 else 0) else 0) := by
      apply pmfMean_congr
      intro table
      by_cases ht : tableHistory query s table n = h <;> simp [tableHistory, hp, ht]
    _ = _ := hh
    _ = _ := by
      apply pmfMean_congr
      intro table
      by_cases ht : tableHistory query s table n = h
      · simp only [if_pos ht, ht]
        apply pmfMean_congr
        intro a
        simp [hp]
      · simp only [if_neg ht]
        symm
        apply (pmfMean_congr _ (fun a => ?_)).trans (pmfMean_const _ 0)
        simp [hp, ht]

def lazyDisclosurePMF (query : ∀ n, FiniteHistory S A n → Key)
    (p : Key → PMF A) (s : S) : (n : ℕ) → PMF (FiniteHistory S A n)
  | 0 => PMF.pure s
  | n + 1 => (lazyDisclosurePMF query p s n).bind (fun h =>
      (disclosurePMF (disclosureCache query n h (query n h)) (p (query n h))).map (fun a => (h, a)))

theorem preallocatedHistoryPMF_eq_lazy (query : ∀ n, FiniteHistory S A n → Key)
    (p : Key → PMF A) (s : S) : ∀ n, preallocatedHistoryPMF query p s n = lazyDisclosurePMF query p s n := by
  intro n
  induction n with
  | zero =>
    change (finitePiPMF p).map (Function.const (Key → A) s) = PMF.pure s
    exact PMF.map_const _ _
  | succ n ih => rw [preallocatedHistoryPMF_succ, lazyDisclosurePMF, ih]

end
end SampleReuse
