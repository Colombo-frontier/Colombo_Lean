import SampleReuse.OracleDerivativeCapsFinish
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

open SecondOrder MeasureTheory
open scoped BigOperators Classical

namespace SampleReuse.OracleProgramStopping
noncomputable section

variable {Q Y O Z : Type}

def requestCharge (flag : Q→Bool) : OracleProgram Q Y O → ℕ×ℕ
  | .done _ => (0,0)
  | .request q _ => if flag q then (1,0) else (0,1)

theorem requestCounts_succ (flag : Q→Bool) (q₀ : Q) (reply : Q→Z→Y)
    (zs : ℕ→Z) (p : OracleProgram Q Y O) (n : ℕ) :
    OracleDerivativeCaps.requestCounts flag reply (n+1) zs p =
      OracleDerivativeCaps.requestCounts flag reply n zs p +
        requestCharge flag (OracleProgram.run q₀ reply zs p n) := by
  induction n generalizing zs p with
  | zero =>
    cases p with
    | done o => rfl
    | request q k => cases h : flag q <;> simp only [OracleDerivativeCaps.requestCounts,OracleProgram.run,requestCharge,h,if_true,Bool.false_eq_true,if_false] <;> rfl
  | succ n ih =>
    cases p with
    | done o => simp only [OracleDerivativeCaps.requestCounts,OracleDerivativeCaps.run_done_program,requestCharge]; rfl
    | request q k =>
      rw [OracleProgram.run_request]
      simp only [OracleDerivativeCaps.requestCounts]
      rw [ih (fun i => zs (i+1)) (k (reply q (zs 0)))]
      cases h : flag q <;> simp only [h,if_true,Bool.false_eq_true,if_false]
      all_goals apply Prod.ext <;> simp only [Prod.fst_add,Prod.snd_add]
      all_goals omega

theorem requestCounts_eq_sum (flag : Q→Bool) (q₀ : Q) (reply : Q→Z→Y)
    (zs : ℕ→Z) (p : OracleProgram Q Y O) (n : ℕ) :
    OracleDerivativeCaps.requestCounts flag reply n zs p =
      ∑ i ∈ Finset.range n, requestCharge flag (OracleProgram.run q₀ reply zs p i) := by
  induction n with
  | zero => simp only [OracleDerivativeCaps.requestCounts,Finset.range_zero,Finset.sum_empty]; rfl
  | succ n ih => rw [requestCounts_succ,ih,Finset.sum_range_succ]

def firstStop (q₀ : Q) (reply : Q→Z→Y) (zs : ℕ→Z) (p : OracleProgram Q Y O)
    (N : ℕ) (hp : OracleProgram.UsesAtMost N p) : ℕ :=
  Nat.find (show ∃ n, OracleProgram.finished (OracleProgram.run q₀ reply zs p n)=true from by
    obtain ⟨o,ho⟩ := OracleProgram.run_done q₀ reply zs hp
    exact ⟨N,by rw [ho]; rfl⟩)

theorem firstStop_le (q₀ : Q) (reply : Q→Z→Y) (zs : ℕ→Z) (p : OracleProgram Q Y O)
    (N : ℕ) (hp : OracleProgram.UsesAtMost N p) : firstStop q₀ reply zs p N hp≤N := by
  apply Nat.find_min'
  obtain ⟨o,ho⟩ := OracleProgram.run_done q₀ reply zs hp
  rw [ho]
  rfl

theorem firstStop_finished (q₀ : Q) (reply : Q→Z→Y) (zs : ℕ→Z) (p : OracleProgram Q Y O)
    (N : ℕ) (hp : OracleProgram.UsesAtMost N p) :
    OracleProgram.finished (OracleProgram.run q₀ reply zs p (firstStop q₀ reply zs p N hp))=true := by
  unfold firstStop
  exact Nat.find_spec (p := fun n => OracleProgram.finished (OracleProgram.run q₀ reply zs p n)=true) _

theorem firstStop_before (q₀ : Q) (reply : Q→Z→Y) (zs : ℕ→Z) (p : OracleProgram Q Y O)
    (N : ℕ) (hp : OracleProgram.UsesAtMost N p) {i : ℕ} (hi : i<firstStop q₀ reply zs p N hp) :
    OracleProgram.finished (OracleProgram.run q₀ reply zs p i)=false :=
  Bool.eq_false_iff.mpr (Nat.find_min _ hi)

theorem firstStop_output_eq (q₀ : Q) (o₀ : O) (reply : Q→Z→Y) (zs : ℕ→Z) (p : OracleProgram Q Y O)
    (N : ℕ) (hp : OracleProgram.UsesAtMost N p) :
    OracleProgram.output o₀ (OracleProgram.run q₀ reply zs p (firstStop q₀ reply zs p N hp)) =
      OracleProgram.output o₀ (OracleProgram.run q₀ reply zs p N) := by
  have hf := firstStop_finished q₀ reply zs p N hp
  cases he : OracleProgram.run q₀ reply zs p (firstStop q₀ reply zs p N hp) with
  | done o =>
    rw [OracleDerivativeCaps.run_done_stable q₀ reply zs p he (firstStop_le q₀ reply zs p N hp)]
  | request q k => simp only [he,OracleProgram.finished] at hf; cases hf

/-- Every prefix element here is a genuine oracle evaluation: this count
ends at the first finished program state, before any interpreter padding. -/
def literalPrefixCounts (flag : Q→Bool) (q₀ : Q) (reply : Q→Z→Y) (zs : ℕ→Z)
    (p : OracleProgram Q Y O) (n : ℕ) : ℕ×ℕ :=
  ∑ i ∈ Finset.range n,
    if flag (OracleProgram.query q₀ (OracleProgram.run q₀ reply zs p i)) then (1,0) else (0,1)

theorem literalPrefixCounts_total (flag : Q→Bool) (q₀ : Q) (reply : Q→Z→Y) (zs : ℕ→Z)
    (p : OracleProgram Q Y O) (n : ℕ) :
    (literalPrefixCounts flag q₀ reply zs p n).1+(literalPrefixCounts flag q₀ reply zs p n).2=n := by
  simp only [literalPrefixCounts,Prod.fst_sum,Prod.snd_sum,← Finset.sum_add_distrib]
  have he (i : ℕ) :
      (if flag (OracleProgram.query q₀ (OracleProgram.run q₀ reply zs p i)) then (1,0) else (0,1)).1 +
        (if flag (OracleProgram.query q₀ (OracleProgram.run q₀ reply zs p i)) then (1,0) else (0,1)).2 = (1:ℕ) := by
    split_ifs <;> rfl
  simp only [he,Finset.sum_const,Finset.card_range,smul_eq_mul,mul_one]

theorem literalPrefixCounts_firstStop (flag : Q→Bool) (q₀ : Q) (reply : Q→Z→Y) (zs : ℕ→Z)
    (p : OracleProgram Q Y O) (N : ℕ) (hp : OracleProgram.UsesAtMost N p) :
    literalPrefixCounts flag q₀ reply zs p (firstStop q₀ reply zs p N hp) =
      OracleDerivativeCaps.requestCounts flag reply (firstStop q₀ reply zs p N hp) zs p := by
  rw [requestCounts_eq_sum flag q₀]
  apply Finset.sum_congr rfl
  intro i hi
  have hf := firstStop_before q₀ reply zs p N hp (Finset.mem_range.mp hi)
  cases he : OracleProgram.run q₀ reply zs p i with
  | done o => simp only [he,OracleProgram.finished] at hf; cases hf
  | request q k => rfl

theorem capped_literal_counts (flag : Q→Bool) (abort : O) (q₀ : Q)
    (reply : Q→Z→Y) (zs : ℕ→Z) (p : OracleProgram Q Y O) (g h : ℕ) :
    let p' := OracleDerivativeCaps.cap flag abort g h p
    let τ := firstStop q₀ reply zs p' (g+h) (OracleDerivativeCaps.cap_usesAtMost flag abort g h p)
    (literalPrefixCounts flag q₀ reply zs p' τ).1≤g ∧
      (literalPrefixCounts flag q₀ reply zs p' τ).2≤h := by
  dsimp only
  rw [literalPrefixCounts_firstStop]
  exact OracleDerivativeCaps.cap_requestCounts_le _ _ _ _ _ _ _ _

/-- The stop decision uses only the private seed and observed replies. -/
theorem observable_halt_measurable {Ξ : Type} [MeasurableSpace Ξ] [MeasurableSpace Q]
    [MeasurableSpace Y] [MeasurableSpace O] (q₀ : Q) (o₀ : O)
    (p : Ξ→OracleProgram Q Y O) (hp : OracleProgram.MeasurableFamily q₀ o₀ p) (n : ℕ) :
    Measurable (fun w : Ξ×(ℕ→Y) => OracleProgram.finished (OracleProgram.readAnswers (p w.1) w.2 n)) :=
  hp.finished n

end
end SampleReuse.OracleProgramStopping
