import SecondOrder.OracleProgramComposition

open SecondOrder

namespace SampleReuse
namespace OracleDerivativeCaps

variable {Q Y O Z : Type}

/-- Stop before a request whose derivative-specific budget is exhausted.
The abort branch performs no oracle evaluation. -/
def cap (flag : Q → Bool) (abort : O) (g h : ℕ) :
    OracleProgram Q Y O → OracleProgram Q Y O
  | .done o => .done o
  | .request q k =>
    if flag q then
      if g = 0 then .done abort else .request q (fun y => cap flag abort (g-1) h (k y))
    else if h = 0 then .done abort else .request q (fun y => cap flag abort g (h-1) (k y))

/-- A branchwise bound on each derivative, valid even for replies outside
the support of the sampling law. -/
def Respects (flag : Q → Bool) (g h : ℕ) : OracleProgram Q Y O → Prop
  | .done _ => True
  | .request q k => if flag q then 0 < g ∧ ∀ y, Respects flag (g-1) h (k y)
    else 0 < h ∧ ∀ y, Respects flag g (h-1) (k y)

theorem cap_respects (flag : Q → Bool) (abort : O) (p : OracleProgram Q Y O) :
    ∀ g h, Respects flag g h (cap flag abort g h p) := by
  induction p with
  | done o => intro g h; trivial
  | request q k ih =>
    intro g h
    by_cases hf : flag q = true
    · by_cases hg : g=0
      · simp only [cap,if_pos hf,if_pos hg,Respects]
      · simp only [cap,if_pos hf,if_neg hg,Respects,if_pos hf]
        exact ⟨Nat.pos_of_ne_zero hg,fun y => ih y (g-1) h⟩
    · by_cases hh : h=0
      · simp only [cap,if_neg hf,if_pos hh,Respects]
      · simp only [cap,if_neg hf,if_neg hh,Respects,if_neg hf]
        exact ⟨Nat.pos_of_ne_zero hh,fun y => ih y g (h-1)⟩

theorem Respects.usesAtMost (flag : Q → Bool) (p : OracleProgram Q Y O) :
    ∀ {g h}, Respects flag g h p → OracleProgram.UsesAtMost (g+h) p := by
  induction p with
  | done o => intro g h hp; simp only [OracleProgram.UsesAtMost]
  | request q k ih =>
    intro g h hp
    by_cases hf : flag q = true
    · simp only [Respects,if_pos hf] at hp
      have he : g+h=(g-1+h)+1 := by omega
      rw [he]
      exact fun y => ih y (hp.2 y)
    · simp only [Respects,if_neg hf] at hp
      have he : g+h=(g+(h-1))+1 := by omega
      rw [he]
      exact fun y => ih y (hp.2 y)

theorem cap_usesAtMost (flag : Q → Bool) (abort : O) (g h : ℕ) (p : OracleProgram Q Y O) :
    OracleProgram.UsesAtMost (g+h) (cap flag abort g h p) :=
  Respects.usesAtMost flag _ (cap_respects flag abort p g h)

/-- Counts real request nodes only. Dummy queries used by the generic
interpreter after completion do not contribute to either evaluation count. -/
def requestCounts (flag : Q → Bool) (reply : Q → Z → Y) :
    ℕ → (ℕ → Z) → OracleProgram Q Y O → ℕ × ℕ
  | 0,_,_ => (0,0)
  | _+1,_,.done _ => (0,0)
  | n+1,zs,.request q k =>
    let c := requestCounts flag reply n (fun i => zs (i+1)) (k (reply q (zs 0)))
    if flag q then (c.1+1,c.2) else (c.1,c.2+1)

theorem requestCounts_le (flag : Q → Bool) (reply : Q → Z → Y) :
    ∀ n zs (p : OracleProgram Q Y O) {g h}, Respects flag g h p →
      (requestCounts flag reply n zs p).1 ≤ g ∧ (requestCounts flag reply n zs p).2 ≤ h := by
  intro n
  induction n with
  | zero => intro zs p g h hp; simp only [requestCounts]; exact ⟨Nat.zero_le _,Nat.zero_le _⟩
  | succ n ih =>
    intro zs p g h hp
    cases p with
    | done o => simp only [requestCounts]; exact ⟨Nat.zero_le _,Nat.zero_le _⟩
    | request q k =>
      by_cases hf : flag q = true
      · simp only [Respects,if_pos hf] at hp
        have hh := ih (fun i => zs (i+1)) (k (reply q (zs 0))) (hp.2 (reply q (zs 0)))
        simp only [requestCounts,if_pos hf]
        exact ⟨by omega,hh.2⟩
      · simp only [Respects,if_neg hf] at hp
        have hh := ih (fun i => zs (i+1)) (k (reply q (zs 0))) (hp.2 (reply q (zs 0)))
        simp only [requestCounts,if_neg hf]
        exact ⟨hh.1,by omega⟩

theorem cap_requestCounts_le (flag : Q → Bool) (abort : O) (reply : Q → Z → Y)
    (zs : ℕ → Z) (g h n : ℕ) (p : OracleProgram Q Y O) :
    (requestCounts flag reply n zs (cap flag abort g h p)).1 ≤ g ∧
      (requestCounts flag reply n zs (cap flag abort g h p)).2 ≤ h :=
  requestCounts_le flag reply n zs _ (cap_respects flag abort p g h)

theorem run_done_program (q₀ : Q) (reply : Q → Z → Y) (zs : ℕ → Z) (o : O) (n : ℕ) :
    OracleProgram.run q₀ reply zs (.done o) n = .done o := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [OracleProgram.run,ih,OracleProgram.advance]

/-- If a real terminating execution fits both caps, it has exactly the same
output under the capped program. No probability or accuracy premise is used. -/
theorem cap_run_agreement (flag : Q → Bool) (abort : O) (q₀ : Q) (reply : Q → Z → Y) :
    ∀ n zs (p : OracleProgram Q Y O) (g h : ℕ) (o : O),
      OracleProgram.run q₀ reply zs p n = .done o →
      (requestCounts flag reply n zs p).1 ≤ g →
      (requestCounts flag reply n zs p).2 ≤ h →
      OracleProgram.run q₀ reply zs (cap flag abort g h p) n = .done o := by
  intro n
  induction n with
  | zero =>
    intro zs p g h o hp hg hh
    change p = .done o at hp
    rw [hp]
    rfl
  | succ n ih =>
    intro zs p g h o hp hg hh
    cases p with
    | done a =>
      simpa only [cap,run_done_program] using hp
    | request q k =>
      rw [OracleProgram.run_request] at hp
      by_cases hf : flag q = true
      · simp only [requestCounts,if_pos hf] at hg hh
        have hgn : g ≠ 0 := by omega
        simp only [cap,if_pos hf,if_neg hgn]
        rw [OracleProgram.run_request]
        exact ih _ _ (g-1) h o hp (by omega) hh
      · simp only [requestCounts,if_neg hf] at hg hh
        have hhn : h ≠ 0 := by omega
        simp only [cap,if_neg hf,if_neg hhn]
        rw [OracleProgram.run_request]
        exact ih _ _ g (h-1) o hp hg (by omega)

end OracleDerivativeCaps
end SampleReuse
