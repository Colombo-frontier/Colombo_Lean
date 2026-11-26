import NCConcave16991.DenseWeakFreshCompilerRun
import NCConcave16991.DenseWeakAdaptiveAlignment
import Mathlib.Data.List.GetD

/-! # The actual bounded optional-row machine has small alignment probability -/

noncomputable section

open scoped BigOperators

namespace NCConcave16991.DenseWeakHiding.FreshCompiler

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {S : Type*} {n m D : ℕ}
  (request : S → Option (Fin n)) (advance : S → Reply D → S)

def traceProbe (hn : 0 < n) (fuel : ℕ) (s : S) (r : ℕ)
    (v : S → Fin D → ℝ) (h : Fin r → Reply D) (a : Fin (fuel + 1)) : Fin D → ℝ :=
  v ((recoveredTrace request advance hn fuel s r h).getD a.val s)

/-- The probability bound is on the original static bank. States are actual
query-before-response or early terminal states of the bounded machine.
The freshness conjunct is a deterministic cache invariant supplied by the
client; no probability estimate or posterior law is assumed. -/
theorem cutTrace_alignment_probability_le (hn : 0 < n) (hm : m ≤ n)
    (hparity : m % 2 = n % 2) (fuel : ℕ) (s : S) (r : ℕ)
    (hrn : r < n) (hbudget : 8 * m + 9 * r ≤ n)
    (hcoef : (32 / 63 : ℝ) * r * ((m : ℝ) / ((n : ℝ) - r)) ^ 2 ≤ 1 / 8000)
    (v : S → Fin D → ℝ) (hv : ∀ x, (∑ j, (v x j) ^ 2) ≤ 1)
    (hD : 512 * Real.log (((fuel + 1 : ℕ) : ℝ) + 2) + 2048 ≤ (D : ℝ)) :
    (columnBankLaw n m D hm).eventMass {bank |
      FreshAlong request advance hn (fun i d ↦ columnBit (bank d) i) (initial fuel s) r ∧
      ∃ x ∈ cutTrace request advance (fun i d ↦ columnBit (bank d) i) r fuel s,
        (5 / 32 : ℝ) * Real.sqrt (D : ℝ) ≤ signedSum (v x) (bankLabels bank)} ≤ 1 / 8 := by
  let next := nextRow request advance hn fuel s
  let probe := traceProbe request advance hn fuel s r v
  have hprob := adaptive_alignment_probability_le hm hparity next hrn hbudget
    (fun t ht h _ ↦ nextRow_fresh request advance hn fuel s t h (by omega))
    hcoef probe (fun h a ↦ hv _) (by omega : 1 ≤ fuel + 1) hD
  apply (FiniteLaw.eventMass_mono (columnBankLaw n m D hm) ?_).trans hprob
  intro bank hb
  obtain ⟨hfr,x,hx,hvx⟩ := hb
  let hist := (RowExperiment.policyExperiment next r).run columnBit bank
  let trace := recoveredTrace request advance hn fuel s r hist
  have hxtrace : x ∈ trace := actual_cutTrace_subset_recovered request advance columnBit bank
    hn fuel s r hfr x hx
  obtain ⟨a,ha⟩ := List.mem_iff_get.mp hxtrace
  have hlen : trace.length ≤ fuel + 1 := recoveredTrace_length_le request advance hn fuel s r hist
  let b : Fin (fuel + 1) := ⟨a.val,a.isLt.trans_le hlen⟩
  change (bankLabels bank,hist) ∈ alignmentEvent probe ((5 / 32 : ℝ) * Real.sqrt (D : ℝ))
  refine ⟨b,?_⟩
  have hprobe : probe hist b = v x := by
    dsimp [probe,traceProbe,b]
    rw [List.getD_eq_get _ s a,ha]
  simpa only [hprobe] using hvx

end NCConcave16991.DenseWeakHiding.FreshCompiler
