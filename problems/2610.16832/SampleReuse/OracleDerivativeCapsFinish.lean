import SampleReuse.OracleDerivativeCounts
import SampleReuse.OracleDerivativeCapsMeasurable

open SecondOrder

namespace SampleReuse.OracleDerivativeCaps
variable {Q Y O Z : Type}

theorem run_done_stable (q₀ : Q) (reply : Q → Z → Y) (zs : ℕ → Z)
    (p : OracleProgram Q Y O) {n m : ℕ} {o : O}
    (ho : OracleProgram.run q₀ reply zs p n = .done o) (hnm : n ≤ m) :
    OracleProgram.run q₀ reply zs p m = .done o := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le hnm
  rw [OracleProgram.run_add,ho,run_done_program]

/-- Reading the capped program at its deterministic total budget returns
the original output whenever the original real request counts fit both caps.
The original terminating index may include ignored post-completion steps. -/
theorem cap_run_at_budget (flag : Q → Bool) (abort : O) (q₀ : Q) (reply : Q → Z → Y)
    (n : ℕ) (zs : ℕ → Z) (p : OracleProgram Q Y O) (g h : ℕ) (o : O)
    (ho : OracleProgram.run q₀ reply zs p n = .done o)
    (hg : (requestCounts flag reply n zs p).1 ≤ g)
    (hh : (requestCounts flag reply n zs p).2 ≤ h) :
    OracleProgram.run q₀ reply zs (cap flag abort g h p) (g+h) = .done o := by
  have hn := cap_run_agreement flag abort q₀ reply n zs p g h o ho hg hh
  obtain ⟨a,ha⟩ := OracleProgram.run_done q₀ reply zs (cap_usesAtMost flag abort g h p)
  have hn' := run_done_stable q₀ reply zs _ hn (le_max_left n (g+h))
  have ha' := run_done_stable q₀ reply zs _ ha (le_max_right n (g+h))
  have he : a=o := OracleProgram.done.inj (ha'.symm.trans hn')
  simpa only [he] using ha

theorem capped_algorithm_output (flag : Q → Bool) (abort : O) (q₀ : Q) (y₀ : Y)
    (reply : Q → Z → Y) (n : ℕ) (zs : ℕ → Z) (p : OracleProgram Q Y O)
    (g h : ℕ) (o : O)
    (ho : OracleProgram.run q₀ reply zs p n = .done o)
    (hg : (requestCounts flag reply n zs p).1 ≤ g)
    (hh : (requestCounts flag reply n zs p).2 ≤ h) :
    oracleAlgorithmOutput (OracleProgram.algorithm q₀ y₀ abort (cap flag abort g h p))
      reply zs (g+h) = o := by
  rw [OracleProgram.algorithm_output,cap_run_at_budget flag abort q₀ reply n zs p g h o ho hg hh]
  rfl

end SampleReuse.OracleDerivativeCaps
