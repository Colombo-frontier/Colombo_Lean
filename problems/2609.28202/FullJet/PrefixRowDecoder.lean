import FullJet.PrefixCoupling
import FullJet.ReplayProtocol

namespace FullJet

def observedRow {n D k : ℕ} (x : FixedTableSample n D k) (i : Fin n) : Fin D → Bool :=
  fun l => decide (i ∈ fixedObservedColumns x.1 x.2 l)

theorem sampledRow_eq_observed {n D k : ℕ} (x : FixedTableSample n D k) (i : Fin n) :
    sampledRow x i = normalizedVector (fun l => rareSign (observedRow x i l)) := by
  apply congrArg normalizedVector
  funext l
  rw [← fixedObservedColumns_sign]
  simp [observedRow, columnSign, rareSign]

noncomputable def prefixRowDecoder {n D k T : ℕ} (j : Fin (T + 1))
    (y : OtherStageSamples n D k (T + 1) j) (ρ lam : ℝ) (p : ℕ)
    (z : Fin n × BlockSpace T (EuclideanSpace ℝ (Fin D))) (b : Fin D → Bool) :
    JetPacket p (BlockSpace T (EuclideanSpace ℝ (Fin D))) :=
  fullJet p (truncatedComponentChain (erasedDirection j y)
    (Function.update (erasedRow j y z.1) j (normalizedVector (fun l => rareSign (b l))))
    ρ lam (prefixLinks T j.val)) z.2

/-- The prefix through the current row has an explicit decoder. It uses
the other stage samples and that selected row, with no current direction. -/
theorem prefixRowDecoder_exact {n D k T : ℕ}
    (x : Fin (T + 1) → FixedTableSample n D k) (j : Fin (T + 1)) (ρ lam : ℝ) (p : ℕ)
    (z : Fin n × BlockSpace T (EuclideanSpace ℝ (Fin D))) :
    truncatedChainOracle (fun l => sampledDirection (x l))
      (fun i l => sampledRow (x l) i) ρ lam p (prefixLinks T j.val) z =
      prefixRowDecoder j (fun l => x l) ρ lam p z (observedRow (x j) z.1) := by
  apply congrArg (fun f => fullJet p f z.2)
  apply truncatedComponentChain_eq_of_visible_data
  · by_cases h : (0 : Fin (T + 1)) = j
    · subst j
      simp only [Function.update_same]
      exact sampledRow_eq_observed _ _
    · simp [Function.update_of_ne h, erasedRow, h]
  · intro l hl
    have hl' := (mem_prefixLinks l).mp hl
    have hne : l.castSucc ≠ j := by intro heq; have := congrArg Fin.val heq; simp at this; omega
    simp [erasedDirection, hne]
  · intro l hl
    by_cases heq : l.succ = j
    · rw [heq, Function.update_same]
      exact sampledRow_eq_observed _ _
    · simp [Function.update_of_ne heq, erasedRow, heq]

noncomputable def prefixRowUpdate {State : Type*} {n D k T p : ℕ}
    (query : State → Fin n × BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (update : State → JetPacket p (BlockSpace T (EuclideanSpace ℝ (Fin D))) → State)
    (j : Fin (T + 1)) (y : OtherStageSamples n D k (T + 1) j) (ρ lam : ℝ)
    (state : State) (b : Fin D → Bool) : State :=
  update state (prefixRowDecoder j y ρ lam p (query state) b)

/-- Every prefix oracle run is exactly a run of the actual Boolean row
oracle. This is a state identity, so it preserves adaptive queries and output. -/
theorem prefixRun_eq_rowRun {State : Type*} {n D k T p : ℕ}
    (query : State → Fin n × BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (update : State → JetPacket p (BlockSpace T (EuclideanSpace ℝ (Fin D))) → State)
    (initial : State) (x : Fin (T + 1) → FixedTableSample n D k)
    (j : Fin (T + 1)) (ρ lam : ℝ) (q : ℕ) :
    oracleRun query update (truncatedChainOracle (fun l => sampledDirection (x l))
      (fun i l => sampledRow (x l) i) ρ lam p (prefixLinks T j.val)) initial q =
      rowStateRun (fun s => (query s).1)
        (prefixRowUpdate query update j (fun l => x l) ρ lam) initial (x j) q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    change update _ _ = prefixRowUpdate query update j (fun l => x l) ρ lam _ _
    rw [prefixRowDecoder_exact, ih]
    rfl

end FullJet
