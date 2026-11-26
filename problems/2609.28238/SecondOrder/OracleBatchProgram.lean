import SecondOrder.MeasurableOracleProgram

open MeasureTheory

namespace SecondOrder
namespace OracleProgram

variable {Ξ Q Y O Z : Type}

theorem run_request (q₀ : Q) (reply : Q → Z → Y) (zs : ℕ → Z)
    (q : Q) (k : Y → OracleProgram Q Y O) (n : ℕ) :
    run q₀ reply zs (.request q k) (n+1)=
      run q₀ reply (fun i => zs (i+1)) (k (reply q (zs 0))) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [run,ih,run]

/-- A batch specified entirely by its queries and a function of its replies.
The finishing function cannot inspect the samples used to generate them. -/
def batch : (n : ℕ) → (Fin n → Q) → ((Fin n → Y) → O) → OracleProgram Q Y O
  | 0, _, finish => .done (finish Fin.elim0)
  | n+1, qs, finish => .request (qs 0)
      (fun y => batch n (fun i => qs i.succ) (fun ys => finish (Fin.cons y ys)))

theorem batch_usesAtMost (n : ℕ) (qs : Fin n → Q) (finish : (Fin n → Y) → O) :
    UsesAtMost n (batch n qs finish) := by
  induction n with
  | zero => trivial
  | succ n ih => exact fun y => ih _ _

/-- Pathwise identification with the finite array of actual fresh replies,
with exactly one charged call for each array coordinate. -/
theorem batch_run (q₀ : Q) (reply : Q → Z → Y) (zs : ℕ → Z)
    (n : ℕ) (qs : Fin n → Q) (finish : (Fin n → Y) → O) :
    run q₀ reply zs (batch n qs finish) n=.done (finish (fun i => reply (qs i) (zs i))) := by
  induction n generalizing zs with
  | zero =>
    simp only [run,batch]
    congr 2
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    rw [batch,run_request,ih]
    congr 2
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · rfl

variable [MeasurableSpace Ξ] [MeasurableSpace Q] [MeasurableSpace Y] [MeasurableSpace O]

theorem batch_measurable (q₀ : Q) (o₀ : O) (n : ℕ)
    (qs : Ξ → Fin n → Q) (finish : Ξ → (Fin n → Y) → O)
    (hq : ∀ i, Measurable (fun ξ => qs ξ i))
    (hf : Measurable (fun w : Ξ × (Fin n → Y) => finish w.1 w.2)) :
    MeasurableFamily q₀ o₀ (fun ξ => batch n (qs ξ) (finish ξ)) := by
  induction n generalizing Ξ with
  | zero =>
    apply measurableFamily_done
    exact hf.comp (measurable_id.prodMk measurable_const)
  | succ n ih =>
    apply measurableFamily_request q₀ o₀ (fun ξ => qs ξ 0) _ (hq 0)
    apply ih
    · intro i
      exact (hq i.succ).comp measurable_fst
    · have hv : Measurable (fun w : (Ξ × Y) × (Fin n → Y) =>
          (Fin.cons w.1.2 w.2 : Fin (n+1) → Y)) := by
        apply measurable_pi_lambda
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact measurable_fst.snd
        · exact (measurable_pi_apply j).comp measurable_snd
      exact hf.comp (measurable_fst.fst.prodMk hv)

theorem batch_algorithm_measurable (q₀ : Q) (y₀ : Y) (o₀ : O) (n : ℕ)
    (qs : Ξ → Fin n → Q) (finish : Ξ → (Fin n → Y) → O)
    (hq : ∀ i, Measurable (fun ξ => qs ξ i))
    (hf : Measurable (fun w : Ξ × (Fin n → Y) => finish w.1 w.2)) :
    MeasurableOracleAlgorithmFamily (fun ξ => algorithm q₀ y₀ o₀ (batch n (qs ξ) (finish ξ))) :=
  algorithm_measurable y₀ (batch_measurable q₀ o₀ n qs finish hq hf)

theorem batch_algorithm_output (q₀ : Q) (y₀ : Y) (o₀ : O)
    (reply : Q → Z → Y) (zs : ℕ → Z) (n : ℕ) (qs : Fin n → Q) (finish : (Fin n → Y) → O) :
    oracleAlgorithmOutput (algorithm q₀ y₀ o₀ (batch n qs finish)) reply zs n=
      finish (fun i => reply (qs i) (zs i)) := by
  rw [algorithm_output,batch_run]
  rfl

end OracleProgram
end SecondOrder
