import FullJet.FirstHitCoupling
import FullJet.UnobservedStages
import FullJet.SequentialAccounting

open scoped InnerProductSpace

namespace FullJet

def prefixLinks (T h : ℕ) : Finset (Fin T) := Finset.univ.filter (fun l => l.val < h)

@[simp] theorem mem_prefixLinks {T h : ℕ} (l : Fin T) :
    l ∈ prefixLinks T h ↔ l.val < h := by simp [prefixLinks]

noncomputable def erasedDirection {n D k T : ℕ} (j : Fin (T + 1))
    (y : OtherStageSamples n D k (T + 1) j) (l : Fin (T + 1)) :
    EuclideanSpace ℝ (Fin D) :=
  if h : l ≠ j then sampledDirection (y ⟨l, h⟩) else 0

noncomputable def erasedRow {n D k T : ℕ} (j : Fin (T + 1))
    (y : OtherStageSamples n D k (T + 1) j) (i : Fin n) (l : Fin (T + 1)) :
    EuclideanSpace ℝ (Fin D) :=
  if h : l ≠ j then sampledRow (y ⟨l, h⟩) i else 0

noncomputable def sampledChainOracle {n D k T : ℕ}
    (x : Fin (T + 1) → FixedTableSample n D k) (ρ lam : ℝ) (p : ℕ) :=
  chainOracle (fun j => sampledDirection (x j)) (fun i j => sampledRow (x j) i) ρ lam p

noncomputable def erasedPrefixOracle {n D k T : ℕ} (j : Fin (T + 1))
    (y : OtherStageSamples n D k (T + 1) j) (ρ lam : ℝ) (p h : ℕ) :=
  truncatedChainOracle (erasedDirection j y) (erasedRow j y) ρ lam p (prefixLinks T h)

/-- A prefix ending strictly before the target row can be evaluated without
any part of that stage's sample. The replacement is an actual function. -/
theorem prefixOracle_eq_erased {n D k T p h : ℕ}
    (x : Fin (T + 1) → FixedTableSample n D k) (j : Fin (T + 1)) (hj : h < j.val)
    (ρ lam : ℝ) :
    truncatedChainOracle (fun l => sampledDirection (x l))
      (fun i l => sampledRow (x l) i) ρ lam p (prefixLinks T h) =
      erasedPrefixOracle j (fun l => x l) ρ lam p h := by
  funext z
  apply congrArg (fun f => fullJet p f z.2)
  apply truncatedComponentChain_eq_of_visible_data
  · have hz : (0 : Fin (T + 1)) ≠ j := by intro heq; have := congrArg Fin.val heq; simp at this; omega
    simp [erasedRow, hz]
  · intro l hl
    have hl' := (mem_prefixLinks l).mp hl
    have hne : l.castSucc ≠ j := by intro heq; have := congrArg Fin.val heq; simp at this; omega
    simp [erasedDirection, hne]
  · intro l hl
    have hl' := (mem_prefixLinks l).mp hl
    have hne : l.succ ≠ j := by intro heq; have := congrArg Fin.val heq; simp at this; omega
    simp [erasedRow, hne]

/-- Agreement is proved along the actual trajectory. In particular the
state at its first crossing also agrees, before that reply is received. -/
theorem sampledRun_eq_erased_before_crossing {State : Type*} {n D k T p h : ℕ}
    (query : State → Fin n × BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (update : State → JetPacket p (BlockSpace T (EuclideanSpace ℝ (Fin D))) → State)
    (initial : State) (x : Fin (T + 1) → FixedTableSample n D k)
    (j : Fin (T + 1)) (hj : h < j.val) (ρ lam : ℝ) (t : ℕ)
    (hclosed : ∀ s < t, ∀ l : Fin T, h ≤ l.val →
      alignment (sampledDirection (x l.castSucc))
        ((query (oracleRun query update (sampledChainOracle x ρ lam p) initial s)).2 l.castSucc) ≤ 5 / 32) :
    oracleRun query update (sampledChainOracle x ρ lam p) initial t =
      oracleRun query update (erasedPrefixOracle j (fun l => x l) ρ lam p h) initial t := by
  symm
  apply oracleRun_eq_of_agree
  intro s hs
  rw [← prefixOracle_eq_erased x j hj ρ lam]
  symm
  apply componentChain_fullJet_eq_truncated
  intro l hl
  exact hclosed s hs l (by simpa using hl)

end FullJet
