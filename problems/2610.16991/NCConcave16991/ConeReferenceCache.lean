import NCConcave16991.ConditionalHaarConeMeasurable

/-! # Actual measurable row/mean caches for the cone reference oracle -/

noncomputable section

namespace NCConcave16991.ConeReferenceCache

open ConeValue ConePrimitives ConeRadial Haar Set MeasureTheory
open scoped BigOperators InnerProductSpace

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

abbrev Rows (E : Type*) (n M : ℕ) := Fin (M + 1) → Fin n → E
abbrev Means (E : Type*) (M : ℕ) := Fin (M + 1) → E

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n M : ℕ}

def putRow (rows : Rows E n M) (j : Fin (M + 1)) (i : Fin n) (a : E) : Rows E n M :=
  Function.update rows j (Function.update (rows j) i a)

def putMean (means : Means E M) (j : Fin (M + 1)) (a : E) : Means E M := Function.update means j a

def rowMeanAt (rows : Rows E n M) (j : Fin (M + 1)) : E :=
  (Real.sqrt (n : ℝ))⁻¹ • ∑ i, rows j i

def releaseMean (rows : Rows E n M) (means : Means E M) (j : Fin (M + 1)) : Means E M :=
  putMean means j (rowMeanAt rows j)

def queryRows (rows : Rows E n M) (i : Fin n) : Means E M := fun j ↦ rows j i

@[simp] theorem putRow_same (rows : Rows E n M) (j : Fin (M + 1)) (i : Fin n) (a : E) :
    putRow rows j i a j i = a := by simp [putRow]

theorem putRow_other_stage (rows : Rows E n M) (j k : Fin (M + 1)) (i : Fin n) (a : E) (hk : k ≠ j) :
    putRow rows j i a k = rows k := by simp [putRow, hk]

@[simp] theorem putMean_same (means : Means E M) (j : Fin (M + 1)) (a : E) :
    putMean means j a j = a := by simp [putMean]

theorem putMean_other (means : Means E M) (j k : Fin (M + 1)) (a : E) (hk : k ≠ j) :
    putMean means j a k = means k := by simp [putMean, hk]

theorem putRow_continuous (j : Fin (M + 1)) (i : Fin n) :
    Continuous (fun p : Rows E n M × E ↦ putRow p.1 j i p.2) :=
  continuous_fst.update j (((continuous_apply j).comp continuous_fst).update i continuous_snd)

theorem putMean_continuous (j : Fin (M + 1)) :
    Continuous (fun p : Means E M × E ↦ putMean p.1 j p.2) := continuous_update j

theorem rowMeanAt_continuous (j : Fin (M + 1)) : Continuous (fun rows : Rows E n M ↦ rowMeanAt rows j) := by
  exact continuous_const.smul (continuous_finset_sum Finset.univ
    (fun i _ ↦ (continuous_apply i).comp (continuous_apply j)))

theorem releaseMean_continuous (j : Fin (M + 1)) :
    Continuous (fun p : Rows E n M × Means E M ↦ releaseMean p.1 p.2 j) :=
  continuous_snd.update j ((rowMeanAt_continuous j).comp continuous_fst)

theorem queryRows_continuous (i : Fin n) : Continuous (fun rows : Rows E n M ↦ queryRows rows i) :=
  continuous_pi (fun j ↦ (continuous_apply i).comp (continuous_apply j))

theorem rowMeanAt_eq_sourceMean (rows : Rows E n M) (w : Fin n → Fin (M + 1) → E)
    (j : Fin (M + 1)) (hrow : ∀ i, rows j i = w i j) : rowMeanAt rows j = sourceMean w j := by
  unfold rowMeanAt sourceMean
  congr 1
  exact Finset.sum_congr rfl (fun i _ ↦ hrow i)

theorem releaseMean_eq_sourceMean (rows : Rows E n M) (means : Means E M)
    (w : Fin n → Fin (M + 1) → E) (j : Fin (M + 1)) (hrow : ∀ i, rows j i = w i j) :
    releaseMean rows means j j = sourceMean w j := by
  rw [releaseMean, putMean_same, rowMeanAt_eq_sourceMean rows w j hrow]

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem putRow_measurable :
    Measurable (fun p : (Fin (M + 1) × Fin n) × (Rows E n M × E) ↦ putRow p.2.1 p.1.1 p.1.2 p.2.2) :=
  measurable_from_prod_countable_right (fun ji ↦ (putRow_continuous ji.1 ji.2).measurable)

theorem putMean_measurable :
    Measurable (fun p : Fin (M + 1) × (Means E M × E) ↦ putMean p.2.1 p.1 p.2.2) :=
  measurable_from_prod_countable_right (fun j ↦ (putMean_continuous j).measurable)

theorem rowMeanAt_measurable : Measurable (fun p : Fin (M + 1) × Rows E n M ↦ rowMeanAt p.2 p.1) :=
  measurable_from_prod_countable_right (fun j ↦ (rowMeanAt_continuous j).measurable)

theorem releaseMean_measurable :
    Measurable (fun p : Fin (M + 1) × (Rows E n M × Means E M) ↦ releaseMean p.2.1 p.2.2 p.1) :=
  measurable_from_prod_countable_right (fun j ↦ (releaseMean_continuous j).measurable)

theorem queryRows_measurable : Measurable (fun p : Fin n × Rows E n M ↦ queryRows p.2 p.1) :=
  measurable_from_prod_countable_right (fun i ↦ (queryRows_continuous i).measurable)

section Composable

variable {X : Type*} [MeasurableSpace X]

@[fun_prop] theorem measurable_putRow {r : X → Rows E n M} {j : X → Fin (M + 1)} {i : X → Fin n} {a : X → E}
    (hr : Measurable r) (hj : Measurable j) (hi : Measurable i) (ha : Measurable a) :
    Measurable (fun x ↦ putRow (r x) (j x) (i x) (a x)) :=
  putRow_measurable.comp ((hj.prodMk hi).prodMk (hr.prodMk ha))

@[fun_prop] theorem measurable_putMean {m : X → Means E M} {j : X → Fin (M + 1)} {a : X → E}
    (hm : Measurable m) (hj : Measurable j) (ha : Measurable a) :
    Measurable (fun x ↦ putMean (m x) (j x) (a x)) := putMean_measurable.comp (hj.prodMk (hm.prodMk ha))

@[fun_prop] theorem measurable_rowMeanAt {r : X → Rows E n M} {j : X → Fin (M + 1)}
    (hr : Measurable r) (hj : Measurable j) : Measurable (fun x ↦ rowMeanAt (r x) (j x)) :=
  rowMeanAt_measurable.comp (hj.prodMk hr)

@[fun_prop] theorem measurable_releaseMean {r : X → Rows E n M} {m : X → Means E M} {j : X → Fin (M + 1)}
    (hr : Measurable r) (hm : Measurable m) (hj : Measurable j) :
    Measurable (fun x ↦ releaseMean (r x) (m x) (j x)) := releaseMean_measurable.comp (hj.prodMk (hr.prodMk hm))

@[fun_prop] theorem measurable_queryRows {r : X → Rows E n M} {i : X → Fin n}
    (hr : Measurable r) (hi : Measurable i) : Measurable (fun x ↦ queryRows (r x) (i x)) :=
  queryRows_measurable.comp (hi.prodMk hr)

end Composable

variable {D : ℝ} {K : KnownDualDomain (ConeProblem.dualDimension E M) D}

abbrev Query (K : KnownDualDomain (ConeProblem.dualDimension E M) D) (n : ℕ) :=
  OracleQuery n (ConeProblem.primalDimension E M) K

def replyFromCache (R q : ℝ) (frontier : ℕ) (means : Means E M) (rows : Rows E n M) (o : Query K n) :
    OracleAnswer (ConeProblem.primalDimension E M) (ConeProblem.dualDimension E M) :=
  (referenceFlatComponent n R q frontier means (queryRows rows o.1) (queryPoint o),
    (gradient (referenceFlatComponent n R q frontier means (queryRows rows o.1)) (queryPoint o)).fst,
    (gradient (referenceFlatComponent n R q frontier means (queryRows rows o.1)) (queryPoint o)).snd)

theorem queryPoint_continuous : Continuous (fun o : Query K n ↦ queryPoint o) :=
  (WithLp.prod_continuous_toLp 2 _ _).comp
    ((continuous_fst.comp continuous_snd).prodMk
      (continuous_subtype_val.comp (continuous_snd.comp continuous_snd)))

theorem replyFromCache_fixedFrontier_measurable (R q : ℝ) (frontier : ℕ) :
    Measurable (fun p : Means E M × Rows E n M × Query K n ↦ replyFromCache R q frontier p.1 p.2.1 p.2.2) := by
  have ho : Measurable (fun p : Means E M × Rows E n M × Query K n ↦ p.2.2) := measurable_snd.comp measurable_snd
  have hr : Measurable (fun p : Means E M × Rows E n M × Query K n ↦ queryRows p.2.1 p.2.2.1) :=
    queryRows_measurable.comp ((measurable_fst.comp ho).prodMk (measurable_fst.comp measurable_snd))
  have hp : Measurable (fun p : Means E M × Rows E n M × Query K n ↦
      ((p.1, queryRows p.2.1 p.2.2.1), queryPoint p.2.2)) :=
    (measurable_fst.prodMk hr).prodMk
      ((queryPoint_continuous (E := E) (M := M) (n := n) (K := K)).measurable.comp ho)
  convert ((referenceResponse_measurable (E := E) (M := M) n R q frontier).comp hp) using 1
  all_goals rfl

theorem replyFromCache_measurable (R q : ℝ) :
    Measurable (fun p : ℕ × (Means E M × Rows E n M × Query K n) ↦ replyFromCache R q p.1 p.2.1 p.2.2.1 p.2.2.2) :=
  measurable_from_prod_countable_right (fun frontier ↦ replyFromCache_fixedFrontier_measurable R q frontier)

@[fun_prop] theorem measurable_replyFromCache {X : Type*} [MeasurableSpace X]
    (R q : ℝ) {f : X → ℕ} {m : X → Means E M} {r : X → Rows E n M} {o : X → Query K n}
    (hf : Measurable f) (hm : Measurable m) (hr : Measurable r) (ho : Measurable o) :
    Measurable (fun x ↦ replyFromCache R q (f x) (m x) (r x) (o x)) :=
  (replyFromCache_measurable R q).comp (hf.prodMk (hm.prodMk (hr.prodMk ho)))

theorem reply_after_putRow_eq_oracle (hn : 0 < n) (L : ℝ) (hL : 0 < L)
    (R : ℝ) (hR : 0 < R) (q : ℝ) (hq : 1 ≤ q)
    (w : Fin n → Fin (M + 1) → E) (hw : ∀ j, Orthonormal ℝ (fun i ↦ w i j))
    (frontier : Fin (M + 1)) (means : Means E M) (rows : Rows E n M)
    (o : Query (ConeProblem.dualDomain E M R hR) n) (a : E) (ha : a = w o.1 frontier)
    (hmeans : ∀ j, j.val < frontier.val → means j = sourceMean w j)
    (hrows : ∀ j, j.val < frontier.val → ∀ i, rows j i = w i j)
    (hgood : ∀ j, frontier.val ≤ j.val →
      ⟪zeta (((ConeProblem.jointCoordinates E M).symm (queryPoint o)).fst.fst j), sourceMean w j⟫_ℝ < 1 / 4 ∧
      |⟪normalizedClockProbe (((ConeProblem.jointCoordinates E M).symm (queryPoint o)).fst.snd j), sourceMean w j⟫_ℝ| < 1 / 2) :
    replyFromCache R q frontier.val means (putRow rows frontier o.1 a) o =
      oracleResponse (ConeProblem.problem hn L hL R hR q hq w hw) o := by
  symm
  apply oracleResponse_eq_reference_known_data hn L hL R hR q hq w hw frontier.val o means
    (queryRows (putRow rows frontier o.1 a) o.1)
  · intro j hj
    exact (hmeans j hj).symm
  · intro j hj
    by_cases hjf : j = frontier
    · subst j
      simpa only [queryRows, putRow_same] using ha.symm
    · have hjlt : j.val < frontier.val := by
        have hne : j.val ≠ frontier.val := fun h ↦ hjf (Fin.ext h)
        omega
      rw [queryRows, putRow_other_stage rows frontier j o.1 a hjf]
      exact (hrows j hjlt o.1).symm
  · exact hgood

end NCConcave16991.ConeReferenceCache
